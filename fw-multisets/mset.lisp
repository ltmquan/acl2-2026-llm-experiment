; MSET -- finite multisets (bags) represented as omaps from elements to
; positive integer multiplicities.
;
; Representation: a bag is an omap::mapp all of whose values are positive
; integers.  The empty map NIL is the empty bag.
;
; Behavior on non-bags: every function treats each bag argument X as
; (bfix X), i.e. any non-bag is treated as the empty bag.  Consequently every
; function respects BEQUIV in each of its bag arguments.  Natural-number
; arguments (N of INSERT-N) are treated as (nfix N).  The list argument of
; FROM-LIST may be any object; its non-cons tail is ignored.

(in-package "MSET")

(include-book "std/omaps/top" :dir :system)
(include-book "std/lists/duplicity" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(local (in-theory (enable omap::assoc-of-head-key)))

;; Abbreviations for the smallest key of an omap and its value.
(defmacro hk (m) `(mv-nth 0 (omap::head ,m)))
(defmacro hv (m) `(mv-nth 1 (omap::head ,m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Recognizer, fixer, equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bag-vals-p ((x omap::mapp))
  :returns (yes/no booleanp)
  :parents nil
  :short "All values of the omap @('x') are positive integers."
  (or (omap::emptyp x)
      (and (posp (omap::head-val x))
           (bag-vals-p (omap::tail x)))))

(define bagp (x)
  :returns (yes/no booleanp)
  :parents nil
  :short "Recognize bags: omaps whose values are positive integers."
  (and (omap::mapp x)
       (bag-vals-p x))
  ///
  (defrule mapp-when-bagp
    (implies (bagp x) (omap::mapp x))
    :rule-classes (:rewrite :forward-chaining))
  (defrule bagp-of-nil
    (bagp nil))
  (defrule bagp-of-tail
    (implies (bagp x) (bagp (omap::tail x)))
    :enable bag-vals-p)
  (defruled bagp-when-not-emptyp
    (implies (and (bagp x) (not (omap::emptyp x)))
             (posp (hv x)))
    :rule-classes
    (:rewrite
     (:rewrite :corollary
      (implies (and (bagp x) (not (omap::emptyp x)))
               (and (integerp (hv x))
                    (< 0 (hv x)))))
     (:linear :corollary
      (implies (and (bagp x) (not (omap::emptyp x)))
               (< 0 (hv x)))))
    :enable bag-vals-p))

(local (in-theory (enable bagp-when-not-emptyp)))

(defrule posp-of-cdr-assoc-when-bagp
  (implies (and (bagp m) (omap::assoc a m))
           (posp (cdr (omap::assoc a m))))
  :rule-classes (:rewrite
                 (:rewrite :corollary
                  (implies (and (bagp m) (omap::assoc a m))
                           (natp (cdr (omap::assoc a m)))))
                 (:rewrite :corollary
                  (implies (and (bagp m) (omap::assoc a m))
                           (< 0 (cdr (omap::assoc a m)))))
                 (:type-prescription :corollary
                  (implies (and (bagp m) (omap::assoc a m))
                           (and (integerp (cdr (omap::assoc a m)))
                                (< 0 (cdr (omap::assoc a m)))))))
  :induct (bag-vals-p m)
  :enable (bag-vals-p omap::assoc))

(local
 (defun bad-key (m)
   (declare (xargs :guard (omap::mapp m)))
   (cond ((omap::emptyp m) nil)
         ((not (posp (omap::head-val m))) (omap::head-key m))
         (t (bad-key (omap::tail m))))))

(local
 (defrule bad-key-works
   (implies (not (bag-vals-p m))
            (and (omap::assoc (bad-key m) m)
                 (not (posp (cdr (omap::assoc (bad-key m) m))))))
   :induct (bad-key m)
   :enable bag-vals-p))

(defrule bagp-of-omap-update
  (implies (and (bagp m) (posp v))
           (bagp (omap::update k v m)))
  :enable bagp
  :disable (bad-key-works posp-of-cdr-assoc-when-bagp)
  :use ((:instance bad-key-works (m (omap::update k v m)))
        (:instance posp-of-cdr-assoc-when-bagp
                   (a (bad-key (omap::update k v m))))))

(defrule bagp-of-omap-delete
  (implies (bagp m)
           (bagp (omap::delete k m)))
  :enable bagp
  :disable (bad-key-works posp-of-cdr-assoc-when-bagp)
  :use ((:instance bad-key-works (m (omap::delete k m)))
        (:instance posp-of-cdr-assoc-when-bagp
                   (a (bad-key (omap::delete k m))))))

(define bfix ((x bagp))
  :returns (b bagp)
  :parents nil
  :short "Fixing function for bags: non-bags are treated as the empty bag."
  (mbe :logic (if (bagp x) x nil)
       :exec x)
  ///
  (defrule bfix-when-bagp
    (implies (bagp x) (equal (bfix x) x)))
  (defrule bfix-of-bfix
    (equal (bfix (bfix x)) (bfix x)))
  (defrule mapp-of-bfix
    (omap::mapp (bfix x))))

(define bequiv ((x bagp) (y bagp))
  :returns (yes/no booleanp)
  :parents nil
  :short "Bag equivalence: equality after @(tsee bfix)."
  (equal (bfix x) (bfix y))
  ///
  (defequiv bequiv)
  (defrule bfix-under-bequiv
    (bequiv (bfix x) x))
  (defcong bequiv equal (bfix x) 1)
  ;; bequiv is the same as equal on bags
  (defrule bequiv-when-bagp
    (implies (and (bagp x) (bagp y))
             (equal (bequiv x y) (equal x y)))))

;; Every function F defined below fixes its bag arguments with BFIX, so
;; (F .. (bfix x) ..) = (F .. x ..).  This macro proves that and the
;; corresponding BEQUIV congruence.
(defmacro bag-congruence (fn formals pos)
  (let* ((var (nth (1- pos) formals))
         (fixed (update-nth (1- pos) `(bfix ,var) formals))
         (var-equiv (acl2::packn-pos (list var '-equiv) var))
         (equivd (update-nth (1- pos) var-equiv formals))
         (name1 (acl2::packn-pos (list fn '-of-bfix- var) fn))
         (name2 (acl2::packn-pos (list fn '-bequiv-congruence-on- var) fn)))
    `(progn
       (defrule ,name1
         (equal (,fn ,@fixed) (,fn ,@formals))
         :enable ,fn)
       (defrule ,name2
         (implies (bequiv ,var ,var-equiv)
                  (equal (,fn ,@formals) (,fn ,@equivd)))
         :rule-classes :congruence
         :enable bequiv
         :disable ,name1
         :use ((:instance ,name1)
               (:instance ,name1 (,var ,var-equiv)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Empty bag
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :returns (b bagp)
  :parents nil
  :short "The empty bag."
  nil)

(define emptyp ((b bagp))
  :returns (yes/no booleanp)
  :parents nil
  :short "Check whether a bag is empty (non-bags are empty)."
  (omap::emptyp (bfix b)))

(bag-congruence emptyp (b) 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Count and membership
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count (a (b bagp))
  :returns (n natp :rule-classes (:rewrite :type-prescription))
  :parents nil
  :short "Multiplicity of @('a') in the bag @('b') (0 if absent)."
  (let ((pair (omap::assoc a (bfix b))))
    (if pair (cdr pair) 0)))

(bag-congruence count (a b) 2)

(defrule count-when-emptyp-bag
  (implies (omap::emptyp (bfix b))
           (equal (count a b) 0))
  :enable count)


(defrule count-of-update-when-bagp
  (implies (and (bagp m) (posp v))
           (equal (count a (omap::update k v m))
                  (if (equal a k) v (count a m))))
  :enable count)

(defrule count-of-omap-delete-when-bagp
  (implies (bagp m)
           (equal (count a (omap::delete k m))
                  (if (equal a k) 0 (count a m))))
  :enable count)

(defruled count-when-bagp-unfold
  ;; Unfold COUNT along the head/tail structure of a bag.  The SYNTAXP
  ;; restriction prevents repeated unfolding of (count a (omap::tail m)).
  (implies (and (syntaxp (symbolp m))
                (bagp m))
           (equal (count a m)
                  (cond ((omap::emptyp m) 0)
                        ((equal a (hk m)) (hv m))
                        (t (count a (omap::tail m))))))
  :enable (count omap::assoc))

(defrule count-of-head-key
  (implies (and (bagp m) (not (omap::emptyp m)))
           (equal (count (mv-nth 0 (omap::head m)) m)
                  (mv-nth 1 (omap::head m))))
  :enable count-when-bagp-unfold)

(defruled count-of-tail-when-not-head
  (implies (and (bagp m)
                (not (equal a (mv-nth 0 (omap::head m)))))
           (equal (count a (omap::tail m))
                  (count a m)))
  :use count-when-bagp-unfold)

(defrule count-of-tail-of-head-key
  (equal (count (mv-nth 0 (omap::head m)) (omap::tail m)) 0)
  :enable (count bfix))

(defruled assoc-when-bagp
  (implies (bagp m)
           (equal (omap::assoc a m)
                  (if (< 0 (count a m))
                      (cons a (count a m))
                    nil)))
  :induct (bag-vals-p m)
  :enable (bag-vals-p omap::assoc count))

(define in (a (b bagp))
  :returns (yes/no booleanp)
  :parents nil
  :short "Check whether @('a') occurs (at least once) in the bag @('b')."
  (if (omap::assoc a (bfix b)) t nil))

(bag-congruence in (a b) 2)

(defrule in-iff-count
  (equal (in a b)
         (< 0 (count a b)))
  :enable (in count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic "set the count" operation (used by the binary operations)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define set-count (a (n natp) (b bagp))
  :returns (b1 bagp)
  :parents nil
  :short "Set the multiplicity of @('a') in @('b') to @('n')."
  (if (zp n)
      (omap::delete a (bfix b))
    (omap::update a n (bfix b))))

(bag-congruence set-count (a n b) 3)

(defrule count-of-set-count
  (equal (count a (set-count k n b))
         (if (equal a k) (nfix n) (count a b)))
  :enable set-count)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Insertion and deletion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert (a (b bagp))
  :returns (b1 bagp)
  :parents nil
  :short "Add one occurrence of @('a') to @('b')."
  (omap::update a (+ 1 (count a b)) (bfix b)))

(bag-congruence insert (a b) 2)

(defrule count-of-insert
  (equal (count a (insert k b))
         (if (equal a k) (+ 1 (count k b)) (count a b)))
  :enable insert)

(define insert-n (a (n natp) (b bagp))
  :returns (b1 bagp)
  :parents nil
  :short "Add @('n') occurrences of @('a') to @('b') (@('n') is @(tsee nfix)ed)."
  (if (zp n)
      (bfix b)
    (omap::update a (+ n (count a b)) (bfix b))))

(bag-congruence insert-n (a n b) 3)

(defrule count-of-insert-n
  (equal (count a (insert-n k n b))
         (if (equal a k) (+ (nfix n) (count k b)) (count a b)))
  :enable insert-n)

(define delete (a (b bagp))
  :returns (b1 bagp)
  :parents nil
  :short "Remove one occurrence of @('a') from @('b') (no change if absent)."
  (let ((c (count a b)))
    (if (<= c 1)
        (omap::delete a (bfix b))
      (omap::update a (- c 1) (bfix b)))))

(bag-congruence delete (a b) 2)

(defrule count-of-delete
  (equal (count a (delete k b))
         (if (equal a k) (nfix (- (count k b) 1)) (count a b)))
  :enable delete)

(define delete-all (a (b bagp))
  :returns (b1 bagp)
  :parents nil
  :short "Remove all occurrences of @('a') from @('b')."
  (omap::delete a (bfix b)))

(bag-congruence delete-all (a b) 2)

(defrule count-of-delete-all
  (equal (count a (delete-all k b))
         (if (equal a k) 0 (count a b)))
  :enable delete-all)

(defrule count-of-empty
  (equal (count a (empty)) 0)
  :enable (empty count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cardinality and support
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define card-aux ((m bagp))
  :returns (n natp :rule-classes (:rewrite :type-prescription))
  :parents nil
  :short "Sum of the values of the bag map @('m')."
  (if (omap::emptyp m)
      0
    (+ (lnfix (omap::head-val m))
       (card-aux (omap::tail m))))
  ///
  ;; Fundamental decomposition lemma.
  (defruled card-aux-decompose
    (implies (bagp m)
             (equal (card-aux m)
                    (+ (count a m) (card-aux (omap::delete a m)))))
    :induct (card-aux m)
    :expand ((omap::delete a m)
             (card-aux m))
    :enable count-when-bagp-unfold
    :prep-lemmas
    ((defrule card-aux-of-update-smaller
       (implies (and (bagp m1)
                     (or (omap::emptyp m1)
                         (acl2::<< k (hk m1))))
                (equal (card-aux (omap::update k v m1))
                       (+ (nfix v) (card-aux m1))))
       :expand ((card-aux (omap::update k v m1)))
       :enable acl2::<<-irreflexive
       :use ((:instance acl2::<<-asymmetric (acl2::x k)
                        (acl2::y (hk m1)))))
     (defrule head-key-of-delete-of-tail
       (implies (and (not (omap::emptyp (omap::delete a (omap::tail m)))))
                (acl2::<< (hk m)
                          (hk (omap::delete a (omap::tail m)))))
       :enable omap::head-key-minimal-3
       :disable (omap::assoc-of-head)
       :use ((:instance omap::assoc-of-head
                        (omap::map (omap::delete a (omap::tail m)))))))))

(define cardinality ((b bagp))
  :returns (n natp :rule-classes (:rewrite :type-prescription))
  :parents nil
  :short "Total number of occurrences (sum of the multiplicities) in @('b')."
  (card-aux (bfix b)))

(bag-congruence cardinality (b) 1)

(defruled cardinality-decompose
  (equal (cardinality b)
         (+ (count a b) (cardinality (delete-all a b))))
  :enable (cardinality delete-all)
  :use ((:instance card-aux-decompose (m (bfix b)))))

(defrule cardinality-of-empty
  (equal (cardinality (empty)) 0)
  :enable (cardinality empty card-aux))

(defrule delete-all-of-insert
  (equal (delete-all a (insert a b))
         (delete-all a b))
  :enable (delete-all insert))

(defrule delete-all-of-delete
  (equal (delete-all a (delete a b))
         (delete-all a b))
  :enable (delete-all delete))

(defrule delete-all-of-insert-n
  (equal (delete-all a (insert-n a n b))
         (delete-all a b))
  :enable (delete-all insert-n))

(defrule cardinality-of-insert
  (equal (cardinality (insert a b))
         (+ 1 (cardinality b)))
  :use ((:instance cardinality-decompose (b (insert a b)))
        (:instance cardinality-decompose (b b))))

(defrule cardinality-of-insert-n
  (equal (cardinality (insert-n a n b))
         (+ (nfix n) (cardinality b)))
  :use ((:instance cardinality-decompose (b (insert-n a n b)))
        (:instance cardinality-decompose (b b))))

(defrule cardinality-of-delete
  (implies (in a b)
           (equal (cardinality (delete a b))
                  (- (cardinality b) 1)))
  :use ((:instance cardinality-decompose (b (delete a b)))
        (:instance cardinality-decompose (b b))))

(define support ((b bagp))
  :returns (s set::setp)
  :parents nil
  :short "The oset of elements occurring in @('b')."
  (omap::keys (bfix b)))

(bag-congruence support (b) 1)

(defrule in-support
  (equal (set::in a (support b))
         (in a b))
  :enable (support in count omap::in-of-keys-to-assoc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sub-bag, extensionality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subbag-witness-aux ((m bagp) (y bagp))
  :parents nil
  :short "First key of @('m') whose value exceeds its count in @('y')."
  (cond ((omap::emptyp m) nil)
        ((< (count (omap::head-key m) y) (lnfix (omap::head-val m)))
         (omap::head-key m))
        (t (subbag-witness-aux (omap::tail m) y)))
  ///
  (defrule subbag-witness-aux-works
    (implies (and (bagp m)
                  (< (count a y) (count a m)))
             (< (count (subbag-witness-aux m y) y)
                (count (subbag-witness-aux m y) m)))
    :induct (subbag-witness-aux m y)
    :enable count-when-bagp-unfold
    :hints (("Subgoal *1/2" :cases ((equal a (hk m))))
            ("Subgoal *1/1" :cases ((equal a (hk m)))))
    :prep-lemmas
    ((defrule lemma
       (implies (and (bagp m)
                     (< (count w y) (count w (omap::tail m))))
                (equal (count w m) (count w (omap::tail m))))
       :cases ((equal w (hk m)))
       :enable count-of-tail-when-not-head))))

(define subbag-witness ((x bagp) (y bagp))
  :parents nil
  :short "An element whose count in @('x') exceeds its count in @('y'), if any."
  (subbag-witness-aux (bfix x) (bfix y)))

(bag-congruence subbag-witness (x y) 1)
(bag-congruence subbag-witness (x y) 2)

(define subbag ((x bagp) (y bagp))
  :returns (yes/no booleanp)
  :parents nil
  :short "Check whether every element occurs in @('x') at most as often as in @('y')."
  (let ((w (subbag-witness x y)))
    (<= (count w x) (count w y))))

(bag-congruence subbag (x y) 1)
(bag-congruence subbag (x y) 2)

(defrule subbag-when-counts-le
  (implies (<= (count (subbag-witness x y) x)
               (count (subbag-witness x y) y))
           (subbag x y))
  :enable subbag)

(defrule count-le-when-subbag
  (implies (subbag x y)
           (<= (count a x) (count a y)))
  :rule-classes (:rewrite :linear)
  :enable (subbag subbag-witness)
  :use ((:instance subbag-witness-aux-works (m (bfix x)) (y (bfix y)))))

(defrule subbag-reflexive
  (subbag x x))

(defrule subbag-transitive
  (implies (and (subbag x y) (subbag y z))
           (subbag x z))
  :disable count-le-when-subbag
  :use ((:instance count-le-when-subbag (a (subbag-witness x z)))
        (:instance count-le-when-subbag (a (subbag-witness x z)) (x y) (y z))))

(define count-diff-witness ((x bagp) (y bagp))
  :parents nil
  :short "An element whose counts in @('x') and @('y') differ, if any."
  (if (subbag x y)
      (subbag-witness y x)
    (subbag-witness x y)))

(bag-congruence count-diff-witness (x y) 1)
(bag-congruence count-diff-witness (x y) 2)

(defruled counts-equal-when-count-diff-witness
  (implies (equal (count (count-diff-witness x y) x)
                  (count (count-diff-witness x y) y))
           (equal (count a x) (count a y)))
  :enable count-diff-witness
  :disable count-le-when-subbag
  :use ((:instance count-le-when-subbag)
        (:instance count-le-when-subbag (x y) (y x))
        (:instance subbag-when-counts-le (x y) (y x))))

(defrule bag-equal-when-all-counts-equal
  (implies (and (bagp x) (bagp y)
                (equal (count (omap::ext-equal-witness x y) x)
                       (count (omap::ext-equal-witness x y) y)))
           (equal x y))
  :rule-classes nil
  :enable (omap::extensionality assoc-when-bagp))

(defrule bag-extensionality-lemma
  (implies (and (bagp x) (bagp y)
                (equal (count (count-diff-witness x y) x)
                       (count (count-diff-witness x y) y)))
           (equal x y))
  :rule-classes nil
  :use ((:instance bag-equal-when-all-counts-equal)
        (:instance counts-equal-when-count-diff-witness
                   (a (omap::ext-equal-witness x y)))))

(defrule subbag-antisymmetric
  ;; Not a rewrite rule (it would rewrite the variable X); see
  ;; SUBBAG-ANTISYMMETRIC-REWRITE below for a rewrite-rule form.
  (implies (and (bagp x) (bagp y)
                (subbag x y) (subbag y x))
           (equal x y))
  :rule-classes nil
  :use ((:instance bag-extensionality-lemma)
        (:instance count-le-when-subbag (a (count-diff-witness x y)))
        (:instance count-le-when-subbag (a (count-diff-witness x y)) (x y) (y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Binary operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sum-aux ((m bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  (if (omap::emptyp m)
      (bfix y)
    (insert-n (omap::head-key m) (lnfix (omap::head-val m))
              (sum-aux (omap::tail m) y)))
  ///
  (defrule count-of-sum-aux
    (implies (bagp m)
             (equal (count a (sum-aux m y))
                    (+ (count a m) (count a y))))
    :induct (sum-aux m y)
    :enable count-when-bagp-unfold)
  (defrule cardinality-of-sum-aux
    (implies (bagp m)
             (equal (cardinality (sum-aux m y))
                    (+ (card-aux m) (cardinality y))))
    :induct (sum-aux m y)
    :enable card-aux))

(define sum ((x bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  :short "Bag sum: multiplicities add."
  (sum-aux (bfix x) (bfix y)))

(bag-congruence sum (x y) 1)
(bag-congruence sum (x y) 2)

(defrule count-of-sum
  (equal (count a (sum x y))
         (+ (count a x) (count a y)))
  :enable sum)

(defrule cardinality-of-sum
  (equal (cardinality (sum x y))
         (+ (cardinality x) (cardinality y)))
  :enable sum
  :prep-lemmas
  ((defrule card-aux-of-bfix
     (equal (card-aux (bfix x)) (cardinality x))
     :enable cardinality)))

(define union-aux ((m bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  (if (omap::emptyp m)
      (bfix y)
    (set-count (omap::head-key m)
               (max (lnfix (omap::head-val m)) (count (omap::head-key m) y))
               (union-aux (omap::tail m) y)))
  ///
  (defrule count-of-union-aux
    (implies (bagp m)
             (equal (count a (union-aux m y))
                    (max (count a m) (count a y))))
    :induct (union-aux m y)
    :enable count-when-bagp-unfold))

(define union ((x bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  :short "Bag union: maximum of multiplicities."
  (union-aux (bfix x) (bfix y)))

(bag-congruence union (x y) 1)
(bag-congruence union (x y) 2)

(defrule count-of-union
  (equal (count a (union x y))
         (max (count a x) (count a y)))
  :enable union)

(define intersect-aux ((m bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  (if (omap::emptyp m)
      nil
    (set-count (omap::head-key m)
               (min (lnfix (omap::head-val m)) (count (omap::head-key m) y))
               (intersect-aux (omap::tail m) y)))
  ///
  (defrule count-of-intersect-aux
    (implies (bagp m)
             (equal (count a (intersect-aux m y))
                    (min (count a m) (count a y))))
    :induct (intersect-aux m y)
    :enable count-when-bagp-unfold))

(define intersect ((x bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  :short "Bag intersection: minimum of multiplicities."
  (intersect-aux (bfix x) (bfix y)))

(bag-congruence intersect (x y) 1)
(bag-congruence intersect (x y) 2)

(defrule count-of-intersect
  (equal (count a (intersect x y))
         (min (count a x) (count a y)))
  :enable intersect)

(define diff-aux ((m bagp) (x bagp))
  :returns (b bagp)
  :parents nil
  (if (omap::emptyp m)
      (bfix x)
    (set-count (omap::head-key m)
               (nfix (- (count (omap::head-key m) x) (lnfix (omap::head-val m))))
               (diff-aux (omap::tail m) x)))
  ///
  (defrule count-of-diff-aux
    (implies (bagp m)
             (equal (count a (diff-aux m x))
                    (nfix (- (count a x) (count a m)))))
    :induct (diff-aux m x)
    :enable count-when-bagp-unfold))

(define diff ((x bagp) (y bagp))
  :returns (b bagp)
  :parents nil
  :short "Bag difference: truncated subtraction of multiplicities."
  (diff-aux (bfix y) (bfix x)))

(bag-congruence diff (x y) 1)
(bag-congruence diff (x y) 2)

(defrule count-of-diff
  (equal (count a (diff x y))
         (nfix (- (count a x) (count a y))))
  :enable diff)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Conversions with lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-list (l)
  :returns (b bagp)
  :parents nil
  :short "The bag of the elements of the list @('l')."
  (if (atom l)
      (empty)
    (insert (car l) (from-list (cdr l)))))

(defrule count-of-from-list
  (equal (count a (from-list l))
         (duplicity a l))
  :induct (from-list l)
  :enable (from-list duplicity))

(define to-list-aux ((m bagp))
  :returns (l true-listp)
  :parents nil
  (if (omap::emptyp m)
      nil
    (append (repeat (lnfix (omap::head-val m)) (omap::head-key m))
            (to-list-aux (omap::tail m))))
  ///
  (local (defrule duplicity-of-repeat
           (equal (duplicity a (repeat n x))
                  (if (equal a x) (nfix n) 0))
           :enable (repeat duplicity)))
  (defrule duplicity-of-to-list-aux
    (implies (bagp m)
             (equal (duplicity a (to-list-aux m))
                    (count a m)))
    :induct (to-list-aux m)
    :enable count-when-bagp-unfold)
  (defrule len-of-to-list-aux
    (equal (len (to-list-aux m))
           (card-aux m))
    :induct (to-list-aux m)
    :enable card-aux))

(define to-list ((b bagp))
  :returns (l true-listp)
  :parents nil
  :short "List of the elements of @('b'), each repeated by its count, in key order."
  (to-list-aux (bfix b)))

(bag-congruence to-list (b) 1)

(defrule duplicity-of-to-list
  (equal (duplicity a (to-list b))
         (count a b))
  :enable to-list)

(defrule len-of-to-list
  (equal (len (to-list b))
         (cardinality b))
  :enable (to-list cardinality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Algebraic laws (proved by extensionality)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-list-of-to-list
  (equal (from-list (to-list b))
         (bfix b))
  :use ((:instance bag-extensionality-lemma
                   (x (from-list (to-list b))) (y (bfix b)))))

(defrule sum-commutative
  (equal (sum y x) (sum x y))
  :use ((:instance bag-extensionality-lemma (x (sum y x)) (y (sum x y)))))

(defrule sum-associative
  (equal (sum (sum x y) z) (sum x (sum y z)))
  :use ((:instance bag-extensionality-lemma
                   (x (sum (sum x y) z)) (y (sum x (sum y z))))))

(defrule union-commutative
  (equal (union y x) (union x y))
  :use ((:instance bag-extensionality-lemma (x (union y x)) (y (union x y)))))

(defrule union-associative
  (equal (union (union x y) z) (union x (union y z)))
  :use ((:instance bag-extensionality-lemma
                   (x (union (union x y) z)) (y (union x (union y z))))))

(defrule intersect-commutative
  (equal (intersect y x) (intersect x y))
  :use ((:instance bag-extensionality-lemma
                   (x (intersect y x)) (y (intersect x y)))))

(defrule intersect-associative
  (equal (intersect (intersect x y) z) (intersect x (intersect y z)))
  :use ((:instance bag-extensionality-lemma
                   (x (intersect (intersect x y) z))
                   (y (intersect x (intersect y z))))))

;; Closure: the :RETURNS specifications above generate the rewrite rules
;; BAGP-OF-EMPTY, BAGP-OF-BFIX, BAGP-OF-INSERT, BAGP-OF-INSERT-N,
;; BAGP-OF-DELETE, BAGP-OF-DELETE-ALL, BAGP-OF-SUM, BAGP-OF-UNION,
;; BAGP-OF-INTERSECT, BAGP-OF-DIFF, BAGP-OF-FROM-LIST (and BAGP-OF-SET-COUNT).

(defrule emptyp-iff-cardinality-zero
  (equal (emptyp b) (equal (cardinality b) 0))
  :enable (emptyp cardinality card-aux)
  :expand ((card-aux (bfix b))))

;; Extensionality, as an (enabled) rewrite rule.  It is placed at the end of
;; the book so that it does not interfere with the proofs above.
(defrule bag-extensionality
  (implies (and (bagp x) (bagp y)
                (equal (count (count-diff-witness x y) x)
                       (count (count-diff-witness x y) y)))
           (equal x y))
  :rule-classes nil
  :by bag-extensionality-lemma)

;; Rewrite-rule forms of extensionality and antisymmetry.  A rule whose
;; conclusion is (EQUAL X Y) would rewrite the variable X, which is illegal,
;; so these rewrite the term (EQUAL X Y) to T in the propositional (IFF)
;; context.  Both are enabled; they only fire when X and Y can be shown to be
;; bags.
(defrule bag-extensionality-rewrite
  (implies (and (bagp x) (bagp y)
                (equal (count (count-diff-witness x y) x)
                       (count (count-diff-witness x y) y)))
           (iff (equal x y) t))
  :use bag-extensionality-lemma)

(defrule subbag-antisymmetric-rewrite
  (implies (and (subbag x y) (subbag y x)
                (bagp x) (bagp y))
           (iff (equal x y) t))
  :use subbag-antisymmetric)
