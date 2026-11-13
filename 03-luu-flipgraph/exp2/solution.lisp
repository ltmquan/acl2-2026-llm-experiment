(in-package "ACL2")

(include-book "defs")

(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;; ================= from pbag =================



;; ---------------------------------------------------------------
;; Part: obag extensionality and algebra
;; ---------------------------------------------------------------

(defthm obag-bagp-cdr
  (implies (obag::bagp x) (obag::bagp (cdr x)))
  :hints (("Goal" :in-theory (enable obag::bagp))))

(defun occs-l (a b)
  (if (consp b)
      (if (equal a (car b)) (+ 1 (occs-l a (cdr b))) (occs-l a (cdr b)))
    0))

(defthm obag-occs-is-occs-l
  (implies (obag::bagp b)
           (equal (obag::occs a b) (occs-l a b)))
  :hints (("Goal" :induct (occs-l a b)
           :in-theory (enable obag::occs obag::head obag::tail
                              obag::emptyp obag::bfix obag::bagp))))

(defthm occs-l-below-head
  (implies (and (obag::bagp b) (consp b) (<< a (car b)))
           (equal (occs-l a b) 0))
  :hints (("Goal" :induct (len b)
           :in-theory (e/d (obag::bagp)))))

(defun bag-wit (x y)
  (cond ((atom x) (car y))
        ((atom y) (car x))
        ((equal (car x) (car y)) (bag-wit (cdr x) (cdr y)))
        ((<< (car x) (car y)) (car x))
        (t (car y))))

(defthm bag-ext-l
  (implies (and (obag::bagp x) (obag::bagp y)
                (equal (occs-l (bag-wit x y) x)
                       (occs-l (bag-wit x y) y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :induct (bag-wit x y)
           :in-theory (enable obag::bagp))
          ("Subgoal *1/5" :use ((:instance occs-l-below-head (a (car y)) (b x))))
          ("Subgoal *1/4" :use ((:instance occs-l-below-head (a (car x)) (b y))))))

(defthm bag-ext
  (implies (and (obag::bagp x) (obag::bagp y)
                (equal (obag::occs (bag-wit x y) x)
                       (obag::occs (bag-wit x y) y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use bag-ext-l)))

(in-theory (disable obag-occs-is-occs-l))

(defthmd bag-equal-rewrite
  (implies (and (obag::bagp x) (obag::bagp y))
           (equal (equal x y)
                  (equal (obag::occs (bag-wit x y) x)
                         (obag::occs (bag-wit x y) y))))
  :hints (("Goal" :use bag-ext)))


(defthm occs-of-insert-r
  (equal (obag::occs x (obag::insert y bag))
         (if (equal x y)
             (1+ (obag::occs x bag))
           (obag::occs x bag)))
  :hints (("Goal" :in-theory (enable obag::occs-of-insert))))

(defthm occs-of-delete-r
  (equal (obag::occs x (obag::delete y bag))
         (if (and (equal x y)
                  (< 0 (obag::occs x bag)))
             (1- (obag::occs x bag))
           (obag::occs x bag)))
  :hints (("Goal" :in-theory (enable obag::occs-of-delete obag::in-alt-def))))

(defthm occs-of-sum-r
  (equal (obag::occs x (obag::sum a b))
         (+ (obag::occs x a) (obag::occs x b)))
  :hints (("Goal" :in-theory (enable obag::occs-of-sum))))

(defthm in-as-occs
  (equal (obag::in x b) (< 0 (obag::occs x b)))
  :hints (("Goal" :in-theory (enable obag::in-alt-def))))

(defthm occs-of-nil
  (equal (obag::occs x nil) 0)
  :hints (("Goal" :in-theory (enable obag::occs))))

(defthm bagp-of-nil (obag::bagp nil)
  :hints (("Goal" :in-theory (enable obag::bagp))))

(defthm occs-of-bfix
  (equal (obag::occs x (obag::bfix b)) (obag::occs x b))
  :hints (("Goal" :in-theory (enable obag::occs obag::emptyp obag::head obag::tail))))

(defthm bagp-of-insert (obag::bagp (obag::insert a s)))
(defthm bagp-of-delete (obag::bagp (obag::delete a s)))
(defthm bagp-of-sum (obag::bagp (obag::sum a s)))


(defthm insert-commute
  (equal (obag::insert a (obag::insert b s))
         (obag::insert b (obag::insert a s)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm delete-insert-same
  (equal (obag::delete a (obag::insert a s))
         (obag::bfix s))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm delete-insert-diff
  (implies (not (equal a b))
           (equal (obag::delete a (obag::insert b s))
                  (obag::insert b (obag::delete a s))))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm insert-delete-in
  (implies (and (obag::bagp s) (< 0 (obag::occs a s)))
           (equal (obag::insert a (obag::delete a s)) s))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm sum-insert
  (equal (obag::sum (obag::insert a x) y)
         (obag::insert a (obag::sum x y)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm sum-nil
  (implies (obag::bagp y)
           (equal (obag::sum nil y) y))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm sum-delete
  (implies (< 0 (obag::occs a x))
           (equal (obag::delete a (obag::sum x y))
                  (obag::sum (obag::delete a x) y)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm sum-assoc
  (equal (obag::sum (obag::sum x y) z)
         (obag::sum x (obag::sum y z)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm sum-comm
  (equal (obag::sum x y) (obag::sum y x))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite)))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm sum-comm2
  (equal (obag::sum x (obag::sum y z)) (obag::sum y (obag::sum x z)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite)))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm sum-insert-2
  (equal (obag::sum x (obag::insert a y))
         (obag::insert a (obag::sum x y)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

;;;; ================= from pmat =================



;; ---------------------------------------------------------------
;; Part: bits, bit lists, bit matrices
;; ---------------------------------------------------------------

(defthm getbit-0-of-bit
  (implies (bitp x) (equal (getbit 0 x) x))
  :hints (("Goal" :in-theory (enable bitp))))



(defthm bitp-car-of-bit-list
  (implies (and (bit-list-p x) (consp x)) (bitp (car x))))

(defthm bit-listnp-rewrite
  (equal (bit-listnp x n)
         (and (bit-list-p x) (equal (len x) (nfix n))))
  :hints (("Goal" :in-theory (enable bit-listnp))))

(defthm bit-list-p-of-repeat
  (implies (bitp b) (bit-list-p (repeat n b)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm bit-list-p-true-listp
  (implies (bit-list-p x) (true-listp x))
  :rule-classes :forward-chaining)

(defthm bit-list-p-of-add
  (bit-list-p (bit-list-add x y))
  :hints (("Goal" :in-theory (enable bit-list-add))))

(defthm bit-list-p-of-scale
  (bit-list-p (bit-list-scale b x))
  :hints (("Goal" :in-theory (enable bit-list-scale))))

(defthm bit-list-p-of-append
  (implies (and (bit-list-p x) (bit-list-p y)) (bit-list-p (append x y))))

(defthm bit-list-p-of-outer
  (bit-list-p (bit-list-outer x y))
  :hints (("Goal" :in-theory (enable bit-list-outer))))

(defthm len-of-bit-list-add
  (equal (len (bit-list-add x y)) (min (len x) (len y)))
  :hints (("Goal" :in-theory (enable bit-list-add))))

(defthm len-of-bit-list-scale
  (equal (len (bit-list-scale b x)) (len x))
  :hints (("Goal" :in-theory (enable bit-list-scale))))

(defthm len-of-bit-list-outer
  (equal (len (bit-list-outer x y)) (* (len x) (len y)))
  :hints (("Goal" :in-theory (enable bit-list-outer))))

(defthm bit-list-add-comm
  (equal (bit-list-add x y) (bit-list-add y x))
  :hints (("Goal" :in-theory (enable bit-list-add)))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm bit-list-add-assoc
  (equal (bit-list-add (bit-list-add x y) z)
         (bit-list-add x (bit-list-add y z)))
  :hints (("Goal" :in-theory (enable bit-list-add))))

(defthm bit-list-add-comm2
  (equal (bit-list-add x (bit-list-add y z))
         (bit-list-add y (bit-list-add x z)))
  :hints (("Goal" :in-theory (disable bit-list-add-assoc)
           :use ((:instance bit-list-add-assoc)
                 (:instance bit-list-add-assoc (x y) (y x))))))

(defun ind-kx (k x)
  (if (consp x) (ind-kx (1- k) (cdr x)) k))

(defthm bit-list-add-zero-left
  (implies (and (bit-list-p x) (<= (len x) (nfix k)))
           (equal (bit-list-add (repeat k 0) x) x))
  :hints (("Goal" :in-theory (e/d (bit-list-add repeat) (bit-list-add-comm))
           :induct (ind-kx k x))))

(defthm bit-list-add-zero-right
  (implies (and (bit-list-p x) (<= (len x) (nfix k)))
           (equal (bit-list-add x (repeat k 0)) x))
  :hints (("Goal" :use bit-list-add-zero-left
           :in-theory (disable bit-list-add-zero-left))))

(defthm bit-list-add-self
  (equal (bit-list-add x x) (repeat (len x) 0))
  :hints (("Goal" :in-theory (enable bit-list-add repeat))))

(defthm bit-list-add-self-2
  (implies (and (bit-list-p y) (<= (len y) (len x)))
           (equal (bit-list-add x (bit-list-add x y)) y))
  :hints (("Goal" :in-theory (e/d (bit-list-add) (bit-list-add-comm bit-list-add-comm2))
           :induct (bit-list-add x y))))

(defthm len-of-repeat
  (equal (len (repeat n x)) (nfix n))
  :hints (("Goal" :in-theory (enable repeat))))

;; matrices

(defthm bit-matp-rewrite-true-listp
  (implies (bit-matp a m n) (true-listp a))
  :hints (("Goal" :in-theory (enable bit-matp)))
  :rule-classes :forward-chaining)

(defthm bit-matp-len
  (implies (bit-matp a m n) (equal (len a) (nfix m)))
  :hints (("Goal" :in-theory (enable bit-matp))))

(defthm bit-matp-bit-list-listp
  (implies (bit-matp a m n) (bit-list-listp a))
  :hints (("Goal" :in-theory (enable bit-matp))))

(defthm bit-matp-of-bit-mat0
  (bit-matp (bit-mat0 m n) m n)
  :hints (("Goal" :in-theory (enable bit-matp bit-mat0 bit-listn0 repeat))))

(defthm bit-matp-of-bit-mat-add
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (bit-matp (bit-mat-add a b) m n))
  :hints (("Goal" :in-theory (enable bit-matp bit-mat-add))))

(defthm bit-mat-add-comm
  (equal (bit-mat-add x y) (bit-mat-add y x))
  :hints (("Goal" :in-theory (enable bit-mat-add)))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm bit-mat-add-assoc
  (equal (bit-mat-add (bit-mat-add x y) z)
         (bit-mat-add x (bit-mat-add y z)))
  :hints (("Goal" :in-theory (enable bit-mat-add))))

(defthm bit-mat-add-comm2
  (equal (bit-mat-add x (bit-mat-add y z))
         (bit-mat-add y (bit-mat-add x z)))
  :hints (("Goal" :in-theory (disable bit-mat-add-assoc)
           :use ((:instance bit-mat-add-assoc)
                 (:instance bit-mat-add-assoc (x y) (y x))))))

(defthm bit-mat-add-self
  (implies (bit-matp a m n)
           (equal (bit-mat-add a a) (bit-mat0 m n)))
  :hints (("Goal" :in-theory (enable bit-matp bit-mat-add bit-mat0 bit-listn0 repeat))))

(defthm bit-mat-add-self-2
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (bit-mat-add a (bit-mat-add a b)) b))
  :hints (("Goal" :in-theory (enable bit-matp bit-mat-add))))

(defthm bit-mat-add-zero-left
  (implies (bit-matp a m n)
           (equal (bit-mat-add (bit-mat0 m n) a) a))
  :hints (("Goal" :in-theory (enable bit-matp bit-mat-add bit-mat0 bit-listn0 repeat))))

(defthm bit-mat-add-zero-right
  (implies (bit-matp a m n)
           (equal (bit-mat-add a (bit-mat0 m n)) a))
  :hints (("Goal" :use bit-mat-add-zero-left :in-theory (disable bit-mat-add-zero-left))))

(defthm bit-list-add-equal-zero
  (implies (and (bit-list-p x) (bit-list-p y) (equal (len x) (len y)))
           (equal (equal (bit-list-add x y) (repeat (len x) 0))
                  (equal x y)))
  :hints (("Goal" :in-theory (e/d (bit-list-add repeat bitp) (bit-list-add-comm bit-list-add-comm2))
           :induct (bit-list-add x y))))

(defun ind-abm (a b m)
  (if (zp m) (list a b) (ind-abm (cdr a) (cdr b) (1- m))))

(defthm bit-mat-add-equal-zero
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (equal (bit-mat-add a b) (bit-mat0 m n))
                  (equal a b)))
  :hints (("Goal" :in-theory (e/d (bit-matp bit-mat-add bit-mat0 bit-listn0 repeat)
                                  (bit-mat-add-comm bit-mat-add-comm2 bit-list-add-comm bit-list-add-equal-zero))
           :induct (ind-abm a b m))
          ("Subgoal *1/2" :use ((:instance bit-list-add-equal-zero (x (car a)) (y (car b)))))))

(defthm bit-mat-add-cancel-right
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (bit-mat-add (bit-mat-add a b) b) a))
  :hints (("Goal" :in-theory (disable bit-mat-add-self-2)
           :use ((:instance bit-mat-add-self-2 (a b) (b a))))))

(defthm bit-mat-add-cancel-equal
  (implies (and (bit-matp a m n) (bit-matp b m n) (bit-matp c m n))
           (equal (equal (bit-mat-add a b) (bit-mat-add a c))
                  (equal b c)))
  :hints (("Goal" :in-theory (disable bit-mat-add-self-2)
           :use ((:instance bit-mat-add-self-2 (b b))
                 (:instance bit-mat-add-self-2 (b c))))))

(defthm bit-mat-add-equal-self
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (equal (bit-mat-add a b) a)
                  (equal b (bit-mat0 m n))))
  :hints (("Goal" :in-theory (disable bit-mat-add-cancel-equal bit-mat-add-zero-right)
           :use ((:instance bit-mat-add-cancel-equal (c (bit-mat0 m n)))
                 (:instance bit-mat-add-zero-right)))))

(defthm bit-mat-add-equal-self-2
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (equal (bit-mat-add b a) a)
                  (equal b (bit-mat0 m n))))
  :hints (("Goal" :in-theory (disable bit-mat-add-equal-self)
           :use ((:instance bit-mat-add-equal-self)))))

;; ---------------------------------------------------------------
;; dimension binding for free variables via bind-free
;; ---------------------------------------------------------------

(mutual-recursion
 (defun find-dim-term (x)
   (declare (xargs :guard t :measure (acl2-count x)))
   (cond ((atom x) nil)
         ((eq (car x) 'quote) nil)
         ((and (member-eq (car x) '(summandp summand-dimp all-dimp summand-listp
                                             correct-schemep schemep))
               (consp (cdr x)) (consp (cddr x)))
          (caddr x))
         ((and (eq (car x) 'all-good-in) (consp (cdr x)) (consp (cddr x))
               (consp (cdddr x)))
          (cadddr x))
         ((and (eq (car x) 'bit-matp) (consp (cdr x)) (consp (cddr x))
               (consp (cdddr x))
               (equal (caddr x) (cadddr x)))
          (caddr x))
         (t (find-dim-list (cdr x)))))
 (defun find-dim-list (l)
   (declare (xargs :guard t :measure (acl2-count l)))
   (if (atom l)
       nil
     (or (find-dim-term (car l))
         (find-dim-list (cdr l))))))

(defun find-dim (mfc state)
  (declare (xargs :stobjs state :guard t) (ignore state))
  (let ((d (find-dim-list (mfc-clause mfc))))
    (if d (list (cons 'm d) (cons 'n d)) nil)))

(defthm bit-mat-add-self-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n))
           (equal (bit-mat-add a a) (bit-mat0 m n))))

(defthm bit-mat-add-self-2-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n) (bit-matp b m n))
           (equal (bit-mat-add a (bit-mat-add a b)) b)))

(defthm bit-mat-add-cancel-right-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n) (bit-matp b m n))
           (equal (bit-mat-add (bit-mat-add a b) b) a)))

(defthm bit-mat-add-cancel-equal-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n) (bit-matp b m n) (bit-matp c m n))
           (equal (equal (bit-mat-add a b) (bit-mat-add a c))
                  (equal b c))))

(defthm bit-mat-add-equal-self-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n) (bit-matp b m n))
           (and (equal (equal (bit-mat-add a b) a)
                       (equal b (bit-mat0 m n)))
                (equal (equal a (bit-mat-add a b))
                       (equal b (bit-mat0 m n)))
                (equal (equal (bit-mat-add b a) a)
                       (equal b (bit-mat0 m n)))
                (equal (equal a (bit-mat-add b a))
                       (equal b (bit-mat0 m n))))))

(defthm bit-mat-add-equal-zero-2
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (equal (bit-mat0 m n) (bit-mat-add a b))
                  (equal a b))))

(in-theory (disable bit-mat-add-self bit-mat-add-self-2 bit-mat-add-cancel-right
                    bit-mat-add-cancel-equal bit-mat-add-equal-self bit-mat-add-equal-self-2))

;;;; ================= from pmove =================



;; ---------------------------------------------------------------
;; Part: summand positions
;; ---------------------------------------------------------------

(in-theory (disable sum-comm sum-comm2))

(defmacro sget (s p) `(summand-get-pos ,s ,p))
(defmacro sset (s p m) `(summand-set-pos ,s ,p ,m))

(defun posp3 (p) (and (natp p) (< p 3)))

(defthm true-listp-len-0
  (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
  :rule-classes :forward-chaining)

(defthm mat-triplep-shape
  (implies (mat-triplep s) (equal (list (car s) (cadr s) (caddr s)) s))
  :hints (("Goal" :expand ((len s) (len (cdr s)) (len (cddr s))))))

(defthm sget-sset-same
  (implies (posp3 p) (equal (sget (sset s p m) p) m)))

(defthm sget-sset-diff
  (implies (and (posp3 p) (posp3 q) (not (equal p q)))
           (equal (sget (sset s p m) q) (sget s q))))

(defthm sset-sset-same
  (implies (posp3 p) (equal (sset (sset s p m) p m2) (sset s p m2))))

(defthm sset-sget-same
  (implies (and (posp3 p) (mat-triplep s)) (equal (sset s p (sget s p)) s))
  :hints (("Goal" :use mat-triplep-shape :in-theory (disable mat-triplep-shape mat-triplep))))

(defthm sset-equal-sset
  (implies (posp3 p)
           (equal (equal (sset s p m) (sset s p m2)) (equal m m2))))

(defthm mat-triplep-sset
  (implies (and (mat-triplep s) (bit-list-listp m))
           (mat-triplep (sset s p m))))

(defthm summandp-sget
  (implies (and (summandp s n) (posp3 p))
           (and (bit-matp (sget s p) n n)
                (not (equal (sget s p) (bit-mat0 n n))))))

(defthm summandp-sset
  (implies (and (summandp s n) (posp3 p) (bit-matp m n n)
                (not (equal m (bit-mat0 n n))))
           (summandp (sset s p m) n)))

(defthm summand0p-sset
  (implies (and (summandp s n) (posp3 p))
           (equal (summand0p (sset s p m) n)
                  (equal m (bit-mat0 n n)))))

(defthm summandp-mat-triplep
  (implies (summandp s n) (mat-triplep s))
  :rule-classes :forward-chaining)

(defthm summand0p-when-summandp
  (implies (summandp s n) (not (summand0p s n))))

(defthm sset-equal-self
  (implies (and (posp3 p) (mat-triplep s))
           (equal (equal (sset s p m) s) (equal m (sget s p))))
  :hints (("Goal" :use mat-triplep-shape :in-theory (disable mat-triplep-shape mat-triplep))))

(defthm sset-sset-diff-equal
  ;; two summands differing at position p are equal iff the p-component equal
  (implies (posp3 p)
           (equal (equal (sset s p m) (sset s2 p m2))
                  (and (equal m m2)
                       (equal (sset s p m) (sset s2 p m)))))
  :rule-classes nil)

(in-theory (disable summand-get-pos summand-set-pos summandp summand0p posp3))

(defthm posp3-forms
  (and (posp3 0) (posp3 1) (posp3 2))
  :hints (("Goal" :in-theory (enable posp3))))

(defthm posp3-pos-next
  (posp3 (pos-next p)) :hints (("Goal" :in-theory (enable posp3))))
(defthm posp3-pos-prev
  (posp3 (pos-prev p)) :hints (("Goal" :in-theory (enable posp3))))

(defthm pos-prev-of-next
  (implies (posp3 p) (equal (pos-prev (pos-next p)) p))
  :hints (("Goal" :in-theory (enable posp3))))

(defthm pos-next-not-self
  (implies (posp3 p) (not (equal (pos-next p) p)))
  :hints (("Goal" :in-theory (enable posp3))))

(defthm pos-next-next-not-self
  (implies (posp3 p) (not (equal (pos-next (pos-next p)) p)))
  :hints (("Goal" :in-theory (enable posp3))))

(defthm pos-next-next-not-next
  (implies (posp3 p) (not (equal (pos-next (pos-next p)) (pos-next p))))
  :hints (("Goal" :in-theory (enable posp3))))

(in-theory (disable pos-next pos-prev))

;; ---------------------------------------------------------------
;; Part: paths
;; ---------------------------------------------------------------

(defthm apply-moves-append
  (equal (apply-moves (append m1 m2) s n)
         (apply-moves m2 (apply-moves m1 s n) n))
  :hints (("Goal" :in-theory (enable apply-moves))))

(defthm path-validp-append
  (equal (path-validp (append m1 m2) s n)
         (and (path-validp m1 s n)
              (path-validp m2 (apply-moves m1 s n) n)))
  :hints (("Goal" :in-theory (enable apply-moves))))

(defthm apply-moves-nil
  (equal (apply-moves nil s n) s)
  :hints (("Goal" :in-theory (enable apply-moves))))

(defthm apply-moves-cons
  (equal (apply-moves (cons m ms) s n)
         (apply-moves ms (apply-move m s n) n))
  :hints (("Goal" :in-theory (enable apply-moves))))

(defthm bagp-apply-move
  (implies (obag::bagp s) (obag::bagp (apply-move m s n)))
  :hints (("Goal" :in-theory (enable apply-move))))

(defthm bagp-apply-moves
  (implies (obag::bagp s) (obag::bagp (apply-moves m s n)))
  :hints (("Goal" :in-theory (enable apply-moves))))

;; frame lemma

(defthm insert-all-nonzero-sum
  (equal (insert-all-nonzero l (obag::sum s j) n)
         (obag::sum (insert-all-nonzero l s n) j)))

(defthm move-validp-sum
  (implies (move-validp m s)
           (move-validp m (obag::sum s j))))

(defthm sum-delete-2
  (implies (< 0 (obag::occs a y))
           (equal (obag::delete a (obag::sum x y))
                  (obag::sum x (obag::delete a y))))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm apply-move-sum
  (implies (and (move-validp m s) (obag::bagp s))
           (equal (apply-move m (obag::sum s j) n)
                  (obag::sum (apply-move m s n) j)))
  :hints (("Goal" :in-theory (enable apply-move))))

(in-theory (disable move-validp))

(defthm frame-lemma
  (implies (and (path-validp ms s n) (obag::bagp s))
           (and (path-validp ms (obag::sum s j) n)
                (equal (apply-moves ms (obag::sum s j) n)
                       (obag::sum (apply-moves ms s n) j))))
  :hints (("Goal" :induct (apply-moves ms s n)
           :in-theory (enable apply-moves))))

(defthm sum-nil-right
  (implies (obag::bagp s) (equal (obag::sum s nil) s))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm frame-pair
  (implies (and (path-validp ms s n) (obag::bagp s))
           (and (path-validp ms (obag::insert a (obag::insert a s)) n)
                (equal (apply-moves ms (obag::insert a (obag::insert a s)) n)
                       (obag::insert a (obag::insert a (apply-moves ms s n))))))
  :hints (("Goal" :use ((:instance frame-lemma
                                   (j (obag::insert a (obag::insert a nil)))))
           :in-theory (disable frame-lemma))))

(in-theory (disable path-validp))

;; ---------------------------------------------------------------
;; Part: single moves
;; ---------------------------------------------------------------

(defun mv-plus (p tt u) (list :plus p tt u))
(defun mv-flip (p s1 s2) (list :flip p s1 s2))

(defthm plus-move-valid
  (implies (and (posp3 p)
                (< 0 (obag::occs tt s)) (< 0 (obag::occs u s))
                (not (equal (sget tt p) (sget u p))))
           (move-validp (mv-plus p tt u) s))
  :hints (("Goal" :in-theory (enable move-validp posp3))))

(defthm plus-move
  (implies (and (obag::bagp s) (posp3 p)
                (summandp tt n) (summandp u n)
                (not (equal (sget tt p) (sget u p))))
           (equal (apply-move (mv-plus p tt u) s n)
                  (obag::insert (sset tt p (bit-mat-add (sget tt p) (sget u p)))
                                (obag::insert (sset tt p (sget u p))
                                              (obag::delete tt s)))))
  :hints (("Goal" :in-theory (enable apply-move move-validp posp3))))

(defthm flip-merge-valid
  (implies (and (posp3 r)
                (< 0 (obag::occs s1 s)) (< 0 (obag::occs s2 s))
                (equal s2 (sset s1 r (sget s2 r)))
                (not (equal (sget s1 r) (sget s2 r))))
           (move-validp (mv-flip (pos-next r) s1 s2) s))
  :hints (("Goal" :in-theory (enable move-validp))))

(defthm flip-merge-move
  ;; s1, s2 agree at positions other than r; merged at r
  (implies (and (obag::bagp s) (posp3 r)
                (summandp s1 n) (summandp s2 n)
                (equal s2 (sset s1 r (sget s2 r)))
                (not (equal (sget s1 r) (sget s2 r))))
           (equal (apply-move (mv-flip (pos-next r) s1 s2) s n)
                  (obag::insert (sset s1 r (bit-mat-add (sget s1 r) (sget s2 r)))
                                (obag::delete s1 (obag::delete s2 s)))))
  :hints (("Goal" :in-theory (enable apply-move move-validp))))

(defthm flip-cancel-valid
  (implies (<= 2 (obag::occs y s))
           (move-validp (mv-flip 0 y y) s))
  :hints (("Goal" :in-theory (enable move-validp))))

(defthm flip-cancel-move
  (implies (and (obag::bagp s)
                (summandp y n))
           (equal (apply-move (mv-flip 0 y y) s n)
                  (obag::delete y (obag::delete y s))))
  :hints (("Goal" :in-theory (enable apply-move move-validp))))

;;;; ================= from pderiv =================



(in-theory (disable insert-commute))

(defthm path-validp-cons
  (equal (path-validp (cons m ms) s n)
         (and (move-validp m s)
              (path-validp ms (apply-move m s n) n)))
  :hints (("Goal" :in-theory (enable path-validp))))

(defthm path-validp-nil
  (path-validp nil s n)
  :hints (("Goal" :in-theory (enable path-validp))))

(defthm path-validp-atom
  (implies (atom ms) (path-validp ms s n))
  :hints (("Goal" :in-theory (enable path-validp))))

(defthm apply-moves-atom
  (implies (atom ms) (equal (apply-moves ms s n) s))
  :hints (("Goal" :in-theory (enable apply-moves))))

;; facts about components of summands

(defthm sget-differ-not-equal
  (implies (not (equal (sget a p) (sget b p)))
           (not (equal a b)))
  :rule-classes ((:forward-chaining :trigger-terms ((equal (sget a p) (sget b p))))))

(defthm sget-add-not-equal-right
  (implies (and (summandp a n) (summandp b n) (posp3 p))
           (not (equal (bit-mat-add (sget a p) (sget b p)) (sget b p))))
  :hints (("Goal" :use ((:instance bit-mat-add-equal-self-2 (a (sget b p)) (b (sget a p)) (m n))))))

(defthm sget-add-not-equal-left
  (implies (and (summandp a n) (summandp b n) (posp3 p))
           (not (equal (bit-mat-add (sget a p) (sget b p)) (sget a p))))
  :hints (("Goal" :use ((:instance bit-mat-add-equal-self (a (sget a p)) (b (sget b p)) (m n))))))

(defthm sget-add-cancel-right
  (implies (and (summandp a n) (summandp b n) (posp3 p))
           (equal (bit-mat-add (bit-mat-add (sget a p) (sget b p)) (sget b p))
                  (sget a p)))
  :hints (("Goal" :use ((:instance bit-mat-add-cancel-right (a (sget a p)) (b (sget b p)) (m n))))))

(defthm sget-add-cancel-left
  (implies (and (summandp a n) (summandp b n) (posp3 p))
           (equal (bit-mat-add (bit-mat-add (sget a p) (sget b p)) (sget a p))
                  (sget b p)))
  :hints (("Goal" :use ((:instance bit-mat-add-cancel-right (a (sget b p)) (b (sget a p)) (m n))))))

(defthm sget-add-self
  (implies (and (summandp a n) (posp3 p))
           (equal (bit-mat-add (sget a p) (sget a p)) (bit-mat0 n n))))

(defthm summandp-sset-add
  (implies (and (summandp c n) (summandp a n) (summandp b n) (posp3 p)
                (not (equal (sget a p) (sget b p))))
           (summandp (sset c p (bit-mat-add (sget a p) (sget b p))) n))
  :hints (("Goal" :use ((:instance bit-mat-add-equal-zero (a (sget a p)) (b (sget b p)) (m n))))))

(defthm summandp-sset-sget
  (implies (and (summandp c n) (summandp a n) (posp3 p))
           (summandp (sset c p (sget a p)) n)))

(defthm summand0p-sset-add
  (implies (and (summandp c n) (summandp a n) (summandp b n) (posp3 p))
           (equal (summand0p (sset c p (bit-mat-add (sget a p) (sget b p))) n)
                  (equal (sget a p) (sget b p))))
  :hints (("Goal" :use ((:instance bit-mat-add-equal-zero (a (sget a p)) (b (sget b p)) (m n))))))

(defthm summand0p-sset-sget
  (implies (and (summandp c n) (summandp a n) (posp3 p))
           (not (summand0p (sset c p (sget a p)) n))))

;; ---------------------------------------------------------------
;; create a pair:  S  -->  S + {Y,Y},  Y = tt with p-component of u
;; ---------------------------------------------------------------

(defun cp-moves (tt u p)
  (list (mv-plus p tt u)
        (mv-plus p (sset tt p (bit-mat-add (sget tt p) (sget u p))) u)))

(defthm cp-moves-lemma
  (implies (and (obag::bagp s) (posp3 p)
                (summandp tt n) (summandp u n)
                (< 0 (obag::occs tt s)) (< 0 (obag::occs u s))
                (not (equal (sget tt p) (sget u p))))
           (and (path-validp (cp-moves tt u p) s n)
                (equal (apply-moves (cp-moves tt u p) s n)
                       (obag::insert (sset tt p (sget u p))
                                     (obag::insert (sset tt p (sget u p)) s)))))
  :hints (("Goal" :in-theory (e/d () (mv-plus)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (bag-equal-rewrite) (mv-plus))))))

;; ---------------------------------------------------------------
;; modify a pair: {Y,Y} --> {Y',Y'}, Y' = Y with p-component of u
;; ---------------------------------------------------------------

(defun mod-moves (y u p)
  (list (mv-plus p y u)
        (mv-plus p y u)
        (mv-flip 0 (sset y p (bit-mat-add (sget y p) (sget u p)))
                 (sset y p (bit-mat-add (sget y p) (sget u p))))))

(defthm mod-moves-lemma
  (implies (and (obag::bagp s) (posp3 p)
                (summandp y n) (summandp u n)
                (<= 2 (obag::occs y s)) (< 0 (obag::occs u s))
                (not (equal (sget y p) (sget u p))))
           (and (path-validp (mod-moves y u p) s n)
                (equal (apply-moves (mod-moves y u p) s n)
                       (obag::insert (sset y p (sget u p))
                                     (obag::insert (sset y p (sget u p))
                                                   (obag::delete y (obag::delete y s)))))))
  :hints (("Goal" :in-theory (e/d () (mv-plus mv-flip)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (bag-equal-rewrite) (mv-plus mv-flip))))))

;; ---------------------------------------------------------------
;; merge two pairs differing only at r
;; ---------------------------------------------------------------

(defun merge2-moves (s1 s2 r)
  (list (mv-flip (pos-next r) s1 s2)
        (mv-flip (pos-next r) s1 s2)))

(defthm merge2-moves-lemma
  (implies (and (obag::bagp s) (posp3 r)
                (summandp s1 n) (summandp s2 n)
                (<= 2 (obag::occs s1 s)) (<= 2 (obag::occs s2 s))
                (equal s2 (sset s1 r (sget s2 r)))
                (not (equal (sget s1 r) (sget s2 r))))
           (and (path-validp (merge2-moves s1 s2 r) s n)
                (equal (apply-moves (merge2-moves s1 s2 r) s n)
                       (obag::insert (sset s1 r (bit-mat-add (sget s1 r) (sget s2 r)))
                                     (obag::insert (sset s1 r (bit-mat-add (sget s1 r) (sget s2 r)))
                                                   (obag::delete s1 (obag::delete s1
                                                     (obag::delete s2 (obag::delete s2 s)))))))))
  :hints (("Goal" :in-theory (e/d () (mv-flip)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (bag-equal-rewrite) (mv-flip))))))

(defthm cancel-move-lemma
  (implies (and (obag::bagp s)
                (summandp y n)
                (<= 2 (obag::occs y s)))
           (and (path-validp (list (mv-flip 0 y y)) s n)
                (equal (apply-moves (list (mv-flip 0 y y)) s n)
                       (obag::delete y (obag::delete y s)))))
  :hints (("Goal" :in-theory (e/d () (mv-flip)))))

;;;; ================= from pacc =================



(defun pm-moves (z base r v)
  (if (equal (sget v r) (sget z r))
      base
    (append base (mod-moves z v r))))

(defthm pm-moves-lemma
  (implies (and (obag::bagp s) (posp3 r)
                (summandp z n) (summandp v n)
                (< 0 (obag::occs v s))
                (path-validp base s n)
                (equal (apply-moves base s n)
                       (obag::insert z (obag::insert z s))))
           (and (path-validp (pm-moves z base r v) s n)
                (equal (apply-moves (pm-moves z base r v) s n)
                       (obag::insert (sset z r (sget v r))
                                     (obag::insert (sset z r (sget v r)) s)))))
  :hints (("Goal" :in-theory (e/d () (mod-moves)))))

(in-theory (disable pm-moves))

(defun msum (vs r n)
  (if (atom vs)
      (bit-mat0 n n)
    (bit-mat-add (sget (car vs) r) (msum (cdr vs) r n))))

(defun all-good-in (vs s n)
  (if (atom vs)
      t
    (and (summandp (car vs) n)
         (< 0 (obag::occs (car vs) s))
         (all-good-in (cdr vs) s n))))

(defthm bit-matp-msum
  (implies (and (all-good-in vs s n) (posp3 r))
           (bit-matp (msum vs r n) n n)))

(defun pstate (s z r acc n)
  (if (equal acc (bit-mat0 n n))
      s
    (obag::insert (sset z r acc) (obag::insert (sset z r acc) s))))

(defun accm (vs z base r acc n)
  (if (atom vs)
      nil
    (let* ((v (car vs))
           (x (sget v r))
           (fa (sset z r acc))
           (fx (sset z r x)))
      (cond ((equal acc (bit-mat0 n n))
             (append (pm-moves z base r v)
                     (accm (cdr vs) z base r x n)))
            ((equal acc x)
             (cons (mv-flip 0 fa fa)
                   (accm (cdr vs) z base r (bit-mat0 n n) n)))
            (t (append (pm-moves z base r v)
                       (append (merge2-moves fa fx r)
                               (accm (cdr vs) z base r (bit-mat-add acc x) n))))))))

(defthm accm-lemma
  (implies (and (obag::bagp s) (posp3 r)
                (summandp z n)
                (path-validp base s n)
                (equal (apply-moves base s n)
                       (obag::insert z (obag::insert z s)))
                (all-good-in vs s n)
                (bit-matp acc n n))
           (and (path-validp (accm vs z base r acc n) (pstate s z r acc n) n)
                (equal (apply-moves (accm vs z base r acc n) (pstate s z r acc n) n)
                       (pstate s z r (bit-mat-add acc (msum vs r n)) n))))
  :hints (("Goal" :induct (accm vs z base r acc n)
           :in-theory (e/d () (merge2-moves mv-flip)))))

;;;; ================= from ppair =================



(defun base0-moves (t0 w)
  (append (cp-moves t0 w 0)
          (mod-moves (sset t0 0 (sget w 0)) t0 0)))

(defthm base0-moves-lemma
  (implies (and (obag::bagp s)
                (summandp t0 n) (summandp w n)
                (< 0 (obag::occs t0 s)) (< 0 (obag::occs w s))
                (not (equal (sget w 0) (sget t0 0))))
           (and (path-validp (base0-moves t0 w) s n)
                (equal (apply-moves (base0-moves t0 w) s n)
                       (obag::insert t0 (obag::insert t0 s)))))
  :hints (("Goal" :in-theory (e/d () (cp-moves mod-moves)))))

(in-theory (disable base0-moves))

(defun pair-moves (x t0 w q0 q1 q2 n)
  (let* ((p1 (accm q0 t0 (base0-moves t0 w) 0 (bit-mat0 n n) n))
         (z0 (sset t0 0 (sget x 0)))
         (p2 (accm q1 z0 p1 1 (bit-mat0 n n) n))
         (z1 (sset z0 1 (sget x 1))))
    (accm q2 z1 p2 2 (bit-mat0 n n) n)))

(defthm sset-three-times
  (implies (and (mat-triplep x) (mat-triplep t0))
           (equal (sset (sset (sset t0 0 (sget x 0)) 1 (sget x 1)) 2 (sget x 2))
                  x))
  :hints (("Goal" :in-theory (enable summand-set-pos summand-get-pos)
           :use ((:instance mat-triplep-shape (s x))))))

(defthm pair-moves-lemma
  (implies (and (obag::bagp s)
                (summandp x n)
                (summandp t0 n) (summandp w n)
                (< 0 (obag::occs t0 s)) (< 0 (obag::occs w s))
                (not (equal (sget w 0) (sget t0 0)))
                (all-good-in q0 s n) (all-good-in q1 s n) (all-good-in q2 s n)
                (equal (msum q0 0 n) (sget x 0))
                (equal (msum q1 1 n) (sget x 1))
                (equal (msum q2 2 n) (sget x 2)))
           (and (path-validp (pair-moves x t0 w q0 q1 q2 n) s n)
                (equal (apply-moves (pair-moves x t0 w q0 q1 q2 n) s n)
                       (obag::insert x (obag::insert x s)))))
  :hints (("Goal" :in-theory (e/d () (accm-lemma accm))
           :use ((:instance accm-lemma (vs q0) (z t0) (base (base0-moves t0 w)) (r 0)
                            (acc (bit-mat0 n n)))
                 (:instance accm-lemma (vs q1) (z (sset t0 0 (sget x 0)))
                            (base (accm q0 t0 (base0-moves t0 w) 0 (bit-mat0 n n) n))
                            (r 1)
                            (acc (bit-mat0 n n)))
                 (:instance accm-lemma (vs q2) (z (sset (sset t0 0 (sget x 0)) 1 (sget x 1)))
                            (base (accm q1 (sset t0 0 (sget x 0))
                                        (accm q0 t0 (base0-moves t0 w) 0 (bit-mat0 n n) n)
                                        1 (bit-mat0 n n) n))
                            (r 2)
                            (acc (bit-mat0 n n)))))))

(in-theory (disable pair-moves))

;;;; ================= from pent =================



;; ---------------------------------------------------------------
;; Part: matrix entries
;; ---------------------------------------------------------------

(defthm nth-of-bit-list-add
  (implies (and (natp j) (< j (len x)) (< j (len y)))
           (equal (nth j (bit-list-add x y))
                  (bitxor (nth j x) (nth j y))))
  :hints (("Goal" :in-theory (enable bit-list-add nth))))

(defthm nth-of-bit-mat-add
  (implies (and (natp i) (< i (len a)) (< i (len b)))
           (equal (nth i (bit-mat-add a b))
                  (bit-list-add (nth i a) (nth i b))))
  :hints (("Goal" :in-theory (enable bit-mat-add nth))))

(defun ind-ami (a m i)
  (if (zp i) (list a m) (ind-ami (cdr a) (1- m) (1- i))))

(defthm bit-matp-nth
  (implies (and (bit-matp a m n) (natp i) (< i m) (natp m))
           (and (bit-list-p (nth i a))
                (equal (len (nth i a)) (nfix n))))
  :hints (("Goal" :in-theory (enable bit-matp nth) :induct (ind-ami a m i))))

(defthm bitp-nth-bit-list
  (implies (and (bit-list-p x) (natp j) (< j (len x)))
           (bitp (nth j x)))
  :hints (("Goal" :in-theory (enable nth))))

(defun ind-jn (j n)
  (if (zp j) n (ind-jn (1- j) (1- n))))

(defthm nth-of-repeat
  (implies (and (natp j) (< j (nfix n)))
           (equal (nth j (repeat n x)) x))
  :hints (("Goal" :in-theory (enable repeat nth) :induct (ind-jn j n))))

(defun ind-ljn (l j n)
  (if (or (zp l) (zp n)) (list j n) (ind-ljn (1- l) (1- j) (1- n))))

(defthm nth-of-bit-unit-list
  (implies (and (natp l) (< l (nfix n)) (natp j))
           (equal (nth l (bit-unit-list j n))
                  (if (equal l j) 1 0)))
  :hints (("Goal" :in-theory (enable bit-unit-list nth bit-listn0) :induct (ind-ljn l j n) :expand ((bit-unit-list j n)))))

(defthm bit-list-p-bit-unit-list
  (bit-list-p (bit-unit-list j n))
  :hints (("Goal" :in-theory (enable bit-unit-list bit-listn0))))

(defthm len-bit-unit-list
  (equal (len (bit-unit-list j n)) (nfix n))
  :hints (("Goal" :in-theory (enable bit-unit-list bit-listn0))))

(defthm nth-of-bit-mat-unit
  (implies (and (natp k) (< k (nfix m)) (natp i))
           (equal (nth k (bit-mat-unit i j m n))
                  (if (equal k i) (bit-unit-list j n) (repeat n 0))))
  :hints (("Goal" :in-theory (enable bit-mat-unit nth bit-mat0 bit-listn0)
           :induct (ind-ljn k i m) :expand ((bit-mat-unit i j m n)))))

(defthm bit-matp-bit-mat-unit
  (bit-matp (bit-mat-unit i j m n) m n)
  :hints (("Goal" :in-theory (enable bit-mat-unit bit-matp bit-listn0))))

(defthm nth-of-bit-mat0
  (implies (and (natp k) (< k (nfix m)))
           (equal (nth k (bit-mat0 m n)) (repeat n 0)))
  :hints (("Goal" :in-theory (enable bit-mat0 bit-listn0))))

(defthm bit-matp-len-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n))
           (equal (len a) (nfix m))))

(defthm bit-matp-nth-bf
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n) (natp i) (< i m) (natp m))
           (and (bit-list-p (nth i a))
                (equal (len (nth i a)) (nfix n)))))

(defthm entry-not-1-is-0
  (implies (and (bit-matp x m n) (natp m) (natp i) (< i m) (natp j) (< j n)
                (natp n)
                (not (equal (nth j (nth i x)) 1)))
           (equal (nth j (nth i x)) 0))
  :hints (("Goal" :in-theory (disable bitp-nth-bit-list bit-matp-nth bit-matp-nth-bf)
           :use ((:instance bitp-nth-bit-list (x (nth i x)))
                 (:instance bit-matp-nth (a x))))))

;; extensionality

(defun lsdiff (x y)
  (cond ((atom x) 0)
        ((atom y) 0)
        ((equal (car x) (car y)) (1+ (lsdiff (cdr x) (cdr y))))
        (t 0)))

(defthm lsdiff-lemma
  (implies (and (true-listp x) (true-listp y) (equal (len x) (len y))
                (not (equal x y)))
           (and (< (lsdiff x y) (len x))
                (not (equal (nth (lsdiff x y) x) (nth (lsdiff x y) y)))))
  :hints (("Goal" :in-theory (enable nth))))

(defun mi (a b) (lsdiff a b))
(defun mj (a b) (lsdiff (nth (mi a b) a) (nth (mi a b) b)))

(defthm mat-ext
  (implies (and (bit-matp a m n) (bit-matp b m n)
                (not (equal a b)))
           (and (natp (mi a b)) (< (mi a b) (nfix m))
                (natp (mj a b)) (< (mj a b) (nfix n))
                (not (equal (nth (mj a b) (nth (mi a b) a))
                            (nth (mj a b) (nth (mi a b) b))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable lsdiff-lemma bit-matp-nth)
           :use ((:instance lsdiff-lemma (x a) (y b))
                 (:instance lsdiff-lemma (x (nth (lsdiff a b) a)) (y (nth (lsdiff a b) b)))
                 (:instance bit-matp-nth (i (lsdiff a b)) (m (nfix m)))
                 (:instance bit-matp-nth (i (lsdiff a b)) (a b) (m (nfix m)))))))

(in-theory (disable mi mj))

;; ---------------------------------------------------------------
;; list sums of matrices and unit decomposition
;; ---------------------------------------------------------------

(defun all-matp (l n)
  (if (atom l) t (and (bit-matp (car l) n n) (all-matp (cdr l) n))))

(defun lsum (l n)
  (if (atom l) (bit-mat0 n n) (bit-mat-add (car l) (lsum (cdr l) n))))

(defthm bit-matp-lsum
  (implies (all-matp l n) (bit-matp (lsum l n) n n)))

(defthm all-matp-append
  (equal (all-matp (append a b) n) (and (all-matp a n) (all-matp b n))))

(defthm lsum-append
  (implies (and (all-matp a n) (all-matp b n))
           (equal (lsum (append a b) n)
                  (bit-mat-add (lsum a n) (lsum b n))))
  :hints (("Goal" :in-theory (enable bit-mat-add-zero-left))))

(defun units-row (x i c n)
  (if (zp c)
      nil
    (if (equal (nth (- n c) (nth i x)) 1)
        (cons (bit-mat-unit i (- n c) n n) (units-row x i (1- c) n))
      (units-row x i (1- c) n))))

(defun units-rows (x c n)
  (if (zp c)
      nil
    (append (units-row x (- n c) n n) (units-rows x (1- c) n))))

(defthm all-matp-units-row
  (all-matp (units-row x i c n) n))

(defthm all-matp-units-rows
  (all-matp (units-rows x c n) n))

(defthm entry-lsum-units-row
  (implies (and (bit-matp x n n) (natp n) (natp i) (< i n) (natp c) (<= c n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (nth l (nth k (lsum (units-row x i c n) n)))
                  (if (and (equal k i) (<= (- n c) l))
                      (nth l (nth k x))
                    0)))
  :hints (("Goal" :induct (units-row x i c n))
          ("Subgoal *1/3" :cases ((< l (- n c)) (equal l (- n c))))
          ("Subgoal *1/2" :cases ((< l (- n c)) (equal l (- n c))))))

(defthm entry-lsum-units-rows
  (implies (and (bit-matp x n n) (natp n) (natp c) (<= c n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (nth l (nth k (lsum (units-rows x c n) n)))
                  (if (<= (- n c) k)
                      (nth l (nth k x))
                    0)))
  :hints (("Goal" :induct (units-rows x c n))
          ("Subgoal *1/2" :cases ((< k (- n c)) (equal k (- n c))))))

(defthm lsum-units-rows
  (implies (and (bit-matp x n n) (natp n))
           (equal (lsum (units-rows x n n) n) x))
  :hints (("Goal" :use ((:instance mat-ext (a (lsum (units-rows x n n) n)) (b x) (m n))))))

;;;; ================= from ptens =================



;; ---------------------------------------------------------------
;; Part: tensor coefficients
;; ---------------------------------------------------------------

(defun tco (k x) (if (equal (nth k x) 1) 1 0))

(defthm bitp-tco (bitp (tco k x)))

(defthm nth-beyond-len
  (implies (and (natp k) (<= (len x) k))
           (equal (nth k x) nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm tco-add
  (implies (and (bit-list-p x) (bit-list-p y) (equal (len x) (len y)) (natp k))
           (equal (tco k (bit-list-add x y))
                  (bitxor (tco k x) (tco k y))))
  :hints (("Goal" :cases ((< k (len x))))
          ("Subgoal 1" :in-theory (disable bitp-nth-bit-list)
           :use ((:instance bitp-nth-bit-list (j k))
                 (:instance bitp-nth-bit-list (j k) (x y))))))

(defthm tco-repeat-0
  (implies (natp k) (equal (tco k (repeat l 0)) 0))
  :hints (("Goal" :cases ((and (natp k) (< k (nfix l)))))))

(defthm nth-of-append-gen
  (implies (natp k)
           (equal (nth k (append x y))
                  (if (< k (len x)) (nth k x) (nth (- k (len x)) y))))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-of-bit-list-scale
  (implies (and (natp j) (< j (len v)))
           (equal (nth j (bit-list-scale b v))
                  (bitand b (nth j v))))
  :hints (("Goal" :in-theory (enable bit-list-scale nth))))

(defthm tco-of-bitp
  (implies (bitp x) (equal (if (equal x 1) 1 0) x))
  :hints (("Goal" :in-theory (enable bitp))))

(defthm mult-ge-self
  (implies (and (integerp a) (< 0 a) (natp l))
           (<= l (* a l)))
  :rule-classes :linear)

(defun ind-outer (a u)
  (if (zp a) u (ind-outer (1- a) (cdr u))))

(defthm tco-outer
  (implies (and (bit-list-p u) (bit-list-p v) (natp a) (natp b) (< b (len v)))
           (equal (tco (+ (* a (len v)) b) (bit-list-outer u v))
                  (bitand (tco a u) (tco b v))))
  :hints (("Goal" :induct (ind-outer a u)
           :in-theory (enable bit-list-outer))
          ("Subgoal *1/2" :expand ((bit-list-outer u v)))
          ("Subgoal *1/1" :expand ((bit-list-outer u v))
           :in-theory (e/d (bit-list-outer) (bitp-nth-bit-list))
           :use ((:instance bitp-nth-bit-list (j b) (x v))))))

;; flat

(defthm len-of-append-x
  (equal (len (append x y)) (+ (len x) (len y))))

(defthm len-mat-flat
  (implies (and (bit-matp a m n) (natp n))
           (equal (len (mat-flat a)) (* (nfix m) n)))
  :hints (("Goal" :in-theory (enable mat-flat bit-matp))))

(defthm bit-list-p-mat-flat
  (implies (bit-list-listp a) (bit-list-p (mat-flat a)))
  :hints (("Goal" :in-theory (enable mat-flat))))

(defthm tco-flat
  (implies (and (bit-matp a m n) (natp m) (natp n)
                (natp i) (< i m) (natp j) (< j n))
           (equal (tco (+ (* i n) j) (mat-flat a))
                  (nth j (nth i a))))
  :hints (("Goal" :induct (ind-ami a m i)
           :in-theory (enable mat-flat bit-matp))
          ("Subgoal *1/1" :in-theory (e/d (mat-flat bit-matp) (bitp-nth-bit-list))
           :expand ((bit-matp a m n) (mat-flat a))
           :use ((:instance bitp-nth-bit-list (x (car a)))))
          ("Subgoal *1/2" :expand ((bit-matp a m n) (mat-flat a)))))

(defthm idx-bound
  (implies (and (natp a) (natp b) (natp aa) (natp bb) (< a aa) (< b bb))
           (< (+ (* a bb) b) (* aa bb)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance (:theorem (implies (and (natp x) (natp y) (natp z) (<= x y))
                                                      (<= (* x z) (* y z))))
                                   (x (+ a 1)) (y aa) (z bb))))))

(defun tidx (i1 j1 i2 j2 i3 j3 n)
  (+ (* (+ (* i1 n) j1) (* (* n n) (* n n)))
     (+ (* (+ (* i2 n) j2) (* n n))
        (+ (* i3 n) j3))))

(defthm tco-tensor
  (implies (and (natp n)
                (bit-matp a n n) (bit-matp b n n) (bit-matp c n n)
                (natp i1) (< i1 n) (natp j1) (< j1 n)
                (natp i2) (< i2 n) (natp j2) (< j2 n)
                (natp i3) (< i3 n) (natp j3) (< j3 n))
           (equal (tco (tidx i1 j1 i2 j2 i3 j3 n) (tensor a b c))
                  (bitand (nth j1 (nth i1 a))
                          (bitand (nth j2 (nth i2 b))
                                  (nth j3 (nth i3 c))))))
  :hints (("Goal" :in-theory (e/d (tensor) (tco tco-outer tco-flat))
           :use ((:instance tco-flat (a a) (m n) (i i1) (j j1))
                 (:instance tco-flat (a b) (m n) (i i2) (j j2))
                 (:instance tco-flat (a c) (m n) (i i3) (j j3))
                 (:instance idx-bound (a i3) (b j3) (aa n) (bb n))
                 (:instance idx-bound (a i2) (b j2) (aa n) (bb n))
                 (:instance idx-bound (a i1) (b j1) (aa n) (bb n))
                 (:instance idx-bound (a (+ (* i2 n) j2)) (b (+ (* i3 n) j3))
                            (aa (* n n)) (bb (* n n)))
                 (:instance tco-outer (u (mat-flat a))
                            (v (bit-list-outer (mat-flat b) (mat-flat c)))
                            (a (+ (* i1 n) j1))
                            (b (+ (* (+ (* i2 n) j2) (* n n)) (+ (* i3 n) j3))))
                 (:instance tco-outer (u (mat-flat b)) (v (mat-flat c))
                            (a (+ (* i2 n) j2))
                            (b (+ (* i3 n) j3)))))))

(in-theory (disable tidx))

;;;; ================= from pmm =================



(defun all-dimp (l n)
  (if (atom l)
      t
    (and (summand-dimp (car l) n)
         (all-dimp (cdr l) n))))

(defthm len-tensor
  (implies (and (natp n) (bit-matp a n n) (bit-matp b n n) (bit-matp c n n))
           (equal (len (tensor a b c)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable tensor))))

(defthm bit-list-p-tensor
  (bit-list-p (tensor a b c))
  :hints (("Goal" :in-theory (enable tensor))))

(defthm len-scheme-sum
  (implies (and (natp n) (all-dimp l n))
           (equal (len (scheme-sum l n)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable scheme-sum bit-listn0))))

(defthm bit-list-p-scheme-sum
  (bit-list-p (scheme-sum l n))
  :hints (("Goal" :in-theory (enable scheme-sum bit-listn0))))

(defun xco (k l)
  (if (atom l)
      0
    (bitxor (tco k (summand-tensor (car l)))
            (xco k (cdr l)))))

(defthm tco-scheme-sum
  (implies (and (natp n) (natp k) (all-dimp l n))
           (equal (tco k (scheme-sum l n)) (xco k l)))
  :hints (("Goal" :in-theory (e/d (scheme-sum bit-listn0) (tco)))))

(defthm natp-tidx
  (implies (and (natp n) (natp i1) (natp j1) (natp i2) (natp j2) (natp i3) (natp j3))
           (natp (tidx i1 j1 i2 j2 i3 j3 n)))
  :hints (("Goal" :in-theory (enable tidx)))
  :rule-classes (:rewrite :type-prescription))

;; mm-tensor

(defthm bit-list-p-mm3 (bit-list-p (mm-tensor-3 i j k n))
  :hints (("Goal" :in-theory (enable mm-tensor-3 bit-listn0))))
(defthm bit-list-p-mm2 (bit-list-p (mm-tensor-2 i j n))
  :hints (("Goal" :in-theory (enable mm-tensor-2 bit-listn0))))
(defthm bit-list-p-mm1 (bit-list-p (mm-tensor-1 i n))
  :hints (("Goal" :in-theory (enable mm-tensor-1 bit-listn0))))

(defthm len-mm3
  (implies (natp n) (equal (len (mm-tensor-3 i j k n)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable mm-tensor-3 bit-listn0))))
(defthm len-mm2
  (implies (natp n) (equal (len (mm-tensor-2 i j n)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable mm-tensor-2 bit-listn0))))
(defthm len-mm1
  (implies (natp n) (equal (len (mm-tensor-1 i n)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable mm-tensor-1 bit-listn0))))

(defmacro idx-hyps ()
  '(and (natp n)
        (natp i1) (< i1 n) (natp j1) (< j1 n)
        (natp i2) (< i2 n) (natp j2) (< j2 n)
        (natp i3) (< i3 n) (natp j3) (< j3 n)))

(defthm tco-mm3
  (implies (and (idx-hyps)
                (natp i) (< i n) (natp j) (< j n) (natp kk) (<= kk n))
           (equal (tco (tidx i1 j1 i2 j2 i3 j3 n) (mm-tensor-3 i j kk n))
                  (if (and (equal i1 i) (equal j1 j) (equal i2 j) (equal i3 i)
                           (equal j2 j3) (< j2 kk))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (mm-tensor-3 bit-listn0) (tco))
           :induct (mm-tensor-3 i j kk n))))

(defthm tco-mm2
  (implies (and (idx-hyps)
                (natp i) (< i n) (natp jj) (<= jj n))
           (equal (tco (tidx i1 j1 i2 j2 i3 j3 n) (mm-tensor-2 i jj n))
                  (if (and (equal i1 i) (equal i3 i) (equal j1 i2)
                           (equal j2 j3) (< j1 jj))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (mm-tensor-2 bit-listn0) (tco))
           :induct (mm-tensor-2 i jj n))))

(defthm tco-mm1
  (implies (and (idx-hyps)
                (natp ii) (<= ii n))
           (equal (tco (tidx i1 j1 i2 j2 i3 j3 n) (mm-tensor-1 ii n))
                  (if (and (equal i1 i3) (equal j1 i2)
                           (equal j2 j3) (< i1 ii))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (mm-tensor-1 bit-listn0) (tco))
           :induct (mm-tensor-1 ii n))))

(defthm tco-mm
  (implies (idx-hyps)
           (equal (tco (tidx i1 j1 i2 j2 i3 j3 n) (mm-tensor n))
                  (if (and (equal i1 i3) (equal j1 i2) (equal j2 j3))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (mm-tensor) (tco)))))

(defthm summand-listp-all-dimp
  (implies (summand-listp l n) (all-dimp l n))
  :hints (("Goal" :in-theory (enable summandp))))

(defthm correct-scheme-coef
  (implies (and (correct-schemep s n) (idx-hyps))
           (equal (xco (tidx i1 j1 i2 j2 i3 j3 n) s)
                  (if (and (equal i1 i3) (equal j1 i2) (equal j2 j3))
                      1 0)))
  :hints (("Goal" :in-theory (e/d (correct-schemep) (tco-scheme-sum tco-mm tco))
           :use ((:instance tco-scheme-sum (k (tidx i1 j1 i2 j2 i3 j3 n)) (l s))
                 (:instance tco-mm)))))

;;;; ================= from pspan =================



(defun filt-cond (x p u v)
  (case p
    (0 (and (equal (nth 0 (nth v (cadr x))) 1) (equal (nth 0 (nth u (caddr x))) 1)))
    (1 (and (equal (nth u (nth 0 (car x))) 1) (equal (nth v (nth 0 (caddr x))) 1)))
    (t (and (equal (nth 0 (nth u (car x))) 1) (equal (nth v (nth 0 (cadr x))) 1)))))

(defun filt (s p u v)
  (cond ((atom s) nil)
        ((filt-cond (car s) p u v) (cons (car s) (filt (cdr s) p u v)))
        (t (filt (cdr s) p u v))))

(defun fidx (p u v k l n)
  (case p
    (0 (tidx k l v 0 u 0 n))
    (1 (tidx 0 u k l 0 v n))
    (t (tidx u 0 0 v k l n))))

(defthm entry-bitp
  (implies (and (bit-matp x m n) (natp m) (natp n)
                (natp i) (< i m) (natp j) (< j n))
           (bitp (nth j (nth i x))))
  :hints (("Goal" :in-theory (disable entry-not-1-is-0)
           :use ((:instance entry-not-1-is-0)))))

(defthm entry-bitp-car1
  (implies (and (bit-matp x m n) (natp m) (natp n)
                (natp i) (< i m) (< 0 n))
           (bitp (car (nth i x))))
  :hints (("Goal" :in-theory (disable entry-bitp entry-not-1-is-0) :use ((:instance entry-bitp (j 0))))))

(defthm entry-bitp-car2
  (implies (and (bit-matp x m n) (natp m) (natp n)
                (< 0 m) (natp j) (< j n))
           (bitp (nth j (car x))))
  :hints (("Goal" :in-theory (disable entry-bitp entry-not-1-is-0) :use ((:instance entry-bitp (i 0))))))

(defthm entry-bitp-car3
  (implies (and (bit-matp x m n) (natp m) (natp n)
                (< 0 m) (< 0 n))
           (bitp (car (car x))))
  :hints (("Goal" :in-theory (disable entry-bitp entry-not-1-is-0) :use ((:instance entry-bitp (i 0) (j 0))))))

(defthmd bitand-as-if
  (implies (and (bitp x) (bitp y))
           (equal (bitand x y) (if (equal x 1) y 0)))
  :hints (("Goal" :in-theory (enable bitp))))

(defthm filt-entry-lemma
  (implies (and (summand-dimp x n) (natp n) (posp3 p)
                (natp k) (< k n) (natp l) (< l n)
                (natp u) (< u n) (natp v) (< v n))
           (equal (tco (fidx p u v k l n) (summand-tensor x))
                  (if (filt-cond x p u v) (nth l (nth k (sget x p))) 0)))
  :hints (("Goal" :in-theory (e/d (posp3 summand-get-pos bitand-as-if) (tco))
           :do-not-induct t
           :cases ((equal p 0) (equal p 1)))))

(in-theory (disable summand-tensor))

(defun xent (l0 p k l)
  (if (atom l0)
      0
    (bitxor (nth l (nth k (sget (car l0) p)))
            (xent (cdr l0) p k l))))

(defthm all-dimp-bit-matp-sget
  (implies (and (summand-dimp x n) (posp3 p))
           (bit-matp (sget x p) n n))
  :hints (("Goal" :in-theory (enable posp3 summand-get-pos))))

(in-theory (disable summand-dimp))

(defthm bit-matp-msum-dimp
  (implies (and (all-dimp l0 n) (posp3 p))
           (bit-matp (msum l0 p n) n n)))

(defthm entry-msum
  (implies (and (all-dimp l0 n) (natp n) (posp3 p)
                (natp k) (< k n) (natp l) (< l n))
           (equal (nth l (nth k (msum l0 p n)))
                  (xent l0 p k l))))

(defun find-n (mfc state)
  (declare (xargs :stobjs state :guard t) (ignore state))
  (let ((d (find-dim-list (mfc-clause mfc))))
    (if d (list (cons 'n d)) nil)))

(defthm filt-xent
  (implies (and (bind-free (find-n mfc state) (n))
                (all-dimp s n) (natp n) (posp3 p)
                (natp k) (< k n) (natp l) (< l n)
                (natp u) (< u n) (natp v) (< v n))
           (equal (xent (filt s p u v) p k l)
                  (xco (fidx p u v k l n) s)))
  :hints (("Goal" :in-theory (e/d () (fidx tco filt-cond)))))

(defthm all-dimp-filt
  (implies (all-dimp s n) (all-dimp (filt s p u v) n)))

(defthm msum-filt
  (implies (and (correct-schemep s n) (natp n) (posp3 p)
                (natp u) (< u n) (natp v) (< v n))
           (equal (msum (filt s p u v) p n)
                  (bit-mat-unit u v n n)))
  :hints (("Goal" :in-theory (e/d (correct-schemep posp3) (filt-cond filt))
           :cases ((equal p 0) (equal p 1) (equal p 2))
           :use ((:instance mat-ext (a (msum (filt s p u v) p n))
                            (b (bit-mat-unit u v n n)) (m n))
                 (:instance correct-scheme-coef
                            (i1 (mi (msum (filt s p u v) p n) (bit-mat-unit u v n n)))
                            (j1 (mj (msum (filt s p u v) p n) (bit-mat-unit u v n n)))
                            (i2 v) (j2 0) (i3 u) (j3 0))
                 (:instance correct-scheme-coef
                            (i2 (mi (msum (filt s p u v) p n) (bit-mat-unit u v n n)))
                            (j2 (mj (msum (filt s p u v) p n) (bit-mat-unit u v n n)))
                            (i1 0) (j1 u) (i3 0) (j3 v))
                 (:instance correct-scheme-coef
                            (i3 (mi (msum (filt s p u v) p n) (bit-mat-unit u v n n)))
                            (j3 (mj (msum (filt s p u v) p n) (bit-mat-unit u v n n)))
                            (i1 u) (j1 0) (i2 0) (j2 v))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (correct-schemep posp3 fidx) (filt-cond filt))))))

;; ---------------------------------------------------------------
;; pivot lists for arbitrary matrices
;; ---------------------------------------------------------------

(defthm msum-atom
  (implies (atom l) (equal (msum l p n) (bit-mat0 n n))))

(defthm correct-schemep-facts
  (implies (correct-schemep s n)
           (and (obag::bagp s) (summand-listp s n) (all-dimp s n)))
  :hints (("Goal" :in-theory (enable correct-schemep))))

(defun q-row (s p x i c n)
  (if (zp c)
      nil
    (if (equal (nth (- n c) (nth i x)) 1)
        (append (filt s p i (- n c)) (q-row s p x i (1- c) n))
      (q-row s p x i (1- c) n))))

(defun q-rows (s p x c n)
  (if (zp c)
      nil
    (append (q-row s p x (- n c) n n) (q-rows s p x (1- c) n))))

(defthm all-dimp-append
  (equal (all-dimp (append a b) n) (and (all-dimp a n) (all-dimp b n))))

(defthm msum-append
  (implies (and (all-dimp a n) (all-dimp b n) (posp3 p))
           (equal (msum (append a b) p n)
                  (bit-mat-add (msum a p n) (msum b p n))))
  :hints (("Goal" :in-theory (enable bit-mat-add-zero-left))))

(defthm all-dimp-q-row
  (implies (all-dimp s n) (all-dimp (q-row s p x i c n) n)))

(defthm all-dimp-q-rows
  (implies (all-dimp s n) (all-dimp (q-rows s p x c n) n)))

(defthm msum-q-row
  (implies (and (correct-schemep s n) (natp n) (posp3 p)
                (natp i) (< i n) (natp c) (<= c n))
           (equal (msum (q-row s p x i c n) p n)
                  (lsum (units-row x i c n) n)))
  :hints (("Goal" :in-theory (e/d () (filt msum)))))

(defthm msum-q-rows
  (implies (and (correct-schemep s n) (natp n) (posp3 p)
                (natp c) (<= c n))
           (equal (msum (q-rows s p x c n) p n)
                  (lsum (units-rows x c n) n)))
  :hints (("Goal" :in-theory (e/d () (filt msum q-row)))))

(defun all-mem (l s)
  (if (atom l) t (and (member-equal (car l) s) (all-mem (cdr l) s))))

(defthm all-mem-cons
  (implies (all-mem l s) (all-mem l (cons a s))))

(defthm all-mem-self
  (all-mem s s))

(defthm all-mem-filt
  (implies (all-mem x y) (all-mem (filt x p u v) y)))

(defthm all-mem-append
  (equal (all-mem (append a b) s) (and (all-mem a s) (all-mem b s))))

(defthm all-mem-q-row
  (all-mem (q-row s p x i c n) s))

(defthm all-mem-q-rows
  (all-mem (q-rows s p x c n) s))

(defthm occs-l-member
  (implies (member-equal a s) (< 0 (occs-l a s))))

(defthm member-occs
  (implies (and (obag::bagp s) (member-equal a s))
           (< 0 (obag::occs a s)))
  :hints (("Goal" :in-theory (enable obag-occs-is-occs-l))))

(defthm member-summand-listp
  (implies (and (summand-listp s n) (member-equal a s))
           (summandp a n)))

(defthm all-mem-all-good-in
  (implies (and (obag::bagp s) (summand-listp s n) (all-mem l s))
           (all-good-in l s n))
  :hints (("Goal" :induct (all-mem l s))))

(defun pivots (s p x n) (q-rows s p x n n))

(defthm pivots-lemma
  (implies (and (correct-schemep s n) (natp n) (posp3 p) (bit-matp x n n))
           (and (all-good-in (pivots s p x n) s n)
                (equal (msum (pivots s p x n) p n) x)))
  :hints (("Goal" :in-theory (e/d () (q-rows)))))

(in-theory (disable pivots))

;; ---------------------------------------------------------------
;; a summand whose 0-component differs from that of the first one
;; ---------------------------------------------------------------

(defun has-diff0 (l a)
  (cond ((atom l) nil)
        ((not (equal (sget (car l) 0) a)) t)
        (t (has-diff0 (cdr l) a))))

(defun find-diff0 (l a)
  (cond ((atom l) nil)
        ((not (equal (sget (car l) 0) a)) (car l))
        (t (find-diff0 (cdr l) a))))

(defthm find-diff0-lemma
  (implies (has-diff0 l a)
           (and (member-equal (find-diff0 l a) l)
                (not (equal (sget (find-diff0 l a) 0) a))))
  :hints (("Goal" :induct (find-diff0 l a))))

(defthm no-diff0-msum
  (implies (and (not (has-diff0 l a)) (all-dimp l n))
           (or (equal (msum (filt l 0 u v) 0 n) a)
               (equal (msum (filt l 0 u v) 0 n) (bit-mat0 n n))))
  :rule-classes nil
  :hints (("Goal" :induct (filt l 0 u v)
           :in-theory (enable bit-mat-add-zero-right))))

(defthm unit-injective
  (implies (and (natp n) (natp i) (< i n) (natp j) (< j n)
                (natp i2) (< i2 n) (natp j2) (< j2 n))
           (equal (equal (bit-mat-unit i j n n) (bit-mat-unit i2 j2 n n))
                  (and (equal i i2) (equal j j2))))
  :hints (("Goal" :use ((:instance (:theorem (implies (equal a b)
                                                      (equal (nth j (nth i a)) (nth j (nth i b)))))
                                   (a (bit-mat-unit i j n n)) (b (bit-mat-unit i2 j2 n n)))))))

(defthm unit-entry-1
  (implies (and (natp n) (natp i) (< i n) (natp j) (< j n))
           (equal (nth j (nth i (bit-mat-unit i j n n))) 1)))

(defthm unit-nonzero
  (implies (and (natp n) (natp i) (< i n) (natp j) (< j n))
           (not (equal (bit-mat-unit i j n n) (bit-mat0 n n))))
  :hints (("Goal" :in-theory (disable unit-entry-1 nth-of-bit-mat-unit)
           :use ((:instance unit-entry-1)))))

(defthm unit-facts
  (implies (and (natp n) (<= 2 n))
           (and (not (equal (bit-mat-unit 0 0 n n) (bit-mat0 n n)))
                (not (equal (bit-mat-unit 0 1 n n) (bit-mat0 n n)))
                (not (equal (bit-mat-unit 0 0 n n) (bit-mat-unit 0 1 n n)))))
  :hints (("Goal" :in-theory (disable unit-injective unit-nonzero)
           :use ((:instance unit-injective (i 0) (j 0) (i2 0) (j2 1))
                 (:instance unit-nonzero (i 0) (j 0))
                 (:instance unit-nonzero (i 0) (j 1))))))

(defthm correct-has-diff0
  (implies (and (correct-schemep s n) (natp n) (<= 2 n))
           (has-diff0 s (sget (car s) 0)))
  :hints (("Goal" :in-theory (e/d (correct-schemep) (has-diff0 msum-filt unit-facts))
           :use ((:instance no-diff0-msum (l s) (a (sget (car s) 0)) (u 0) (v 0))
                 (:instance no-diff0-msum (l s) (a (sget (car s) 0)) (u 0) (v 1))
                 (:instance msum-filt (p 0) (u 0) (v 0))
                 (:instance msum-filt (p 0) (u 0) (v 1))
                 (:instance unit-facts)))))

(defthm correct-consp
  (implies (and (correct-schemep s n) (natp n) (<= 2 n))
           (consp s))
  :rule-classes nil
  :hints (("Goal" :use correct-has-diff0 :in-theory (disable correct-has-diff0))))

;; ---------------------------------------------------------------
;; pair for an arbitrary summand
;; ---------------------------------------------------------------

(defun xpair-moves (x s n)
  (pair-moves x (car s) (find-diff0 s (sget (car s) 0))
              (pivots s 0 (sget x 0) n)
              (pivots s 1 (sget x 1) n)
              (pivots s 2 (sget x 2) n)
              n))

(defthm xpair-moves-lemma
  (implies (and (correct-schemep s n) (natp n) (<= 2 n) (summandp x n))
           (and (path-validp (xpair-moves x s n) s n)
                (equal (apply-moves (xpair-moves x s n) s n)
                       (obag::insert x (obag::insert x s)))))
  :hints (("Goal" :in-theory (e/d (correct-schemep) (pair-moves-lemma find-diff0 has-diff0
                                                     correct-has-diff0 find-diff0-lemma))
           :use ((:instance pair-moves-lemma (t0 (car s)) (w (find-diff0 s (sget (car s) 0)))
                            (q0 (pivots s 0 (sget x 0) n))
                            (q1 (pivots s 1 (sget x 1) n))
                            (q2 (pivots s 2 (sget x 2) n)))
                 (:instance correct-has-diff0)
                 (:instance correct-consp)
                 (:instance find-diff0-lemma (l s) (a (sget (car s) 0)))
                 (:instance member-summand-listp (a (car s)))
                 (:instance member-summand-listp (a (find-diff0 s (sget (car s) 0))))
                 (:instance member-occs (a (car s)))
                 (:instance member-occs (a (find-diff0 s (sget (car s) 0))))))))

(in-theory (disable xpair-moves))

;;;; ================= from plin =================



;; ---------------------------------------------------------------
;; multilinearity of the tensor
;; ---------------------------------------------------------------

(defthm bit-list-add-append
  (implies (equal (len x1) (len x2))
           (equal (bit-list-add (append x1 y1) (append x2 y2))
                  (append (bit-list-add x1 x2) (bit-list-add y1 y2))))
  :hints (("Goal" :in-theory (e/d (bit-list-add) (bit-list-add-comm bit-list-add-comm2))
           :induct (bit-list-add x1 x2))))

(defthm mat-flat-add
  (implies (and (bit-matp a m n) (bit-matp b m n))
           (equal (mat-flat (bit-mat-add a b))
                  (bit-list-add (mat-flat a) (mat-flat b))))
  :hints (("Goal" :in-theory (e/d (mat-flat bit-mat-add bit-matp) (bit-list-add-comm bit-list-add-comm2))
           :induct (ind-abm a b m))))

(defthm bitand-bitxor-dist
  (implies (and (bitp b) (bitp x) (bitp y))
           (equal (bitand b (bitxor x y))
                  (bitxor (bitand b x) (bitand b y))))
  :hints (("Goal" :in-theory (enable bitp))))

(defthm bitand-bitxor-dist-2
  (implies (and (bitp b) (bitp x) (bitp y))
           (equal (bitand (bitxor x y) b)
                  (bitxor (bitand x b) (bitand y b))))
  :hints (("Goal" :in-theory (enable bitp))))

(defthm scale-add-dist
  (implies (and (bitp b) (bit-list-p x) (bit-list-p y))
           (equal (bit-list-scale b (bit-list-add x y))
                  (bit-list-add (bit-list-scale b x) (bit-list-scale b y))))
  :hints (("Goal" :in-theory (e/d (bit-list-scale bit-list-add) (bit-list-add-comm bit-list-add-comm2)))))

(defthm scale-0
  (equal (bit-list-scale 0 v) (repeat (len v) 0))
  :hints (("Goal" :in-theory (enable bit-list-scale repeat))))

(defthm scale-1
  (implies (bit-list-p v) (equal (bit-list-scale 1 v) v))
  :hints (("Goal" :in-theory (enable bit-list-scale))))

(defthm scale-bitxor-dist
  (implies (and (bitp a) (bitp b) (bit-list-p v))
           (equal (bit-list-scale (bitxor a b) v)
                  (bit-list-add (bit-list-scale a v) (bit-list-scale b v))))
  :hints (("Goal" :in-theory (e/d (bit-list-scale bit-list-add) (bit-list-add-comm bit-list-add-comm2)))))

(defthm outer-add-left
  (implies (and (equal (len u1) (len u2)) (bit-list-p u1) (bit-list-p u2) (bit-list-p v))
           (equal (bit-list-outer (bit-list-add u1 u2) v)
                  (bit-list-add (bit-list-outer u1 v) (bit-list-outer u2 v))))
  :hints (("Goal" :in-theory (e/d (bit-list-outer bit-list-add) (bit-list-add-comm bit-list-add-comm2))
           :induct (bit-list-add u1 u2))))

(defthm outer-add-right
  (implies (and (equal (len v1) (len v2)) (bit-list-p u) (bit-list-p v1) (bit-list-p v2))
           (equal (bit-list-outer u (bit-list-add v1 v2))
                  (bit-list-add (bit-list-outer u v1) (bit-list-outer u v2))))
  :hints (("Goal" :in-theory (e/d (bit-list-outer) (bit-list-add-comm bit-list-add-comm2)))))

(defthm tensor-add-0
  (implies (and (natp n) (bit-matp a1 n n) (bit-matp a2 n n) (bit-matp b n n) (bit-matp c n n))
           (equal (tensor (bit-mat-add a1 a2) b c)
                  (bit-list-add (tensor a1 b c) (tensor a2 b c))))
  :hints (("Goal" :in-theory (enable tensor))))

(defthm tensor-add-1
  (implies (and (natp n) (bit-matp a n n) (bit-matp b1 n n) (bit-matp b2 n n) (bit-matp c n n))
           (equal (tensor a (bit-mat-add b1 b2) c)
                  (bit-list-add (tensor a b1 c) (tensor a b2 c))))
  :hints (("Goal" :in-theory (enable tensor))))

(defthm tensor-add-2
  (implies (and (natp n) (bit-matp a n n) (bit-matp b n n) (bit-matp c1 n n) (bit-matp c2 n n))
           (equal (tensor a b (bit-mat-add c1 c2))
                  (bit-list-add (tensor a b c1) (tensor a b c2))))
  :hints (("Goal" :in-theory (enable tensor))))

(defthm summand-tensor-sset-add
  (implies (and (natp n) (summand-dimp w n) (posp3 p) (bit-matp x n n) (bit-matp y n n))
           (equal (summand-tensor (sset w p (bit-mat-add x y)))
                  (bit-list-add (summand-tensor (sset w p x))
                                (summand-tensor (sset w p y)))))
  :hints (("Goal" :in-theory (enable summand-tensor summand-set-pos posp3 summand-dimp)
           :cases ((equal p 0) (equal p 1)))))

(defthm summand-dimp-when-summandp
  (implies (summandp s n) (summand-dimp s n))
  :hints (("Goal" :in-theory (enable summandp summand-dimp))))

(defthm len-summand-tensor
  (implies (and (natp n) (summand-dimp s n))
           (equal (len (summand-tensor s)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable summand-tensor summand-dimp))))

(defthm bit-list-p-summand-tensor
  (bit-list-p (summand-tensor s))
  :hints (("Goal" :in-theory (enable summand-tensor))))

;;;; ================= from pred1 =================



;; ---------------------------------------------------------------
;; adding pairs for every element of a list
;; ---------------------------------------------------------------

(defun all-summandp (l n)
  (if (atom l) t (and (summandp (car l) n) (all-summandp (cdr l) n))))

(defun dbl (l)
  (if (atom l)
      nil
    (obag::insert (car l) (obag::insert (car l) (dbl (cdr l))))))

(defun addp-moves (l s n)
  (if (atom l)
      nil
    (append (xpair-moves (car l) s n)
            (addp-moves (cdr l) s n))))

(defun addp-ind (l j)
  (if (atom l) j (addp-ind (cdr l) (obag::insert (car l) (obag::insert (car l) j)))))

(defthm addp-moves-lemma
  (implies (and (correct-schemep s n) (natp n) (<= 2 n)
                (all-summandp l n) (obag::bagp j))
           (and (path-validp (addp-moves l s n) (obag::sum s j) n)
                (equal (apply-moves (addp-moves l s n) (obag::sum s j) n)
                       (obag::sum s (obag::sum (dbl l) j)))))
  :hints (("Goal" :induct (addp-ind l j)
           :in-theory (e/d () (xpair-moves-lemma frame-lemma)))
          ("Subgoal *1/2" :use ((:instance xpair-moves-lemma (x (car l)))
                                (:instance frame-lemma (ms (xpair-moves (car l) s n)))))))

;; ---------------------------------------------------------------
;; inserting all elements of a list
;; ---------------------------------------------------------------

(defun ins-all (l b)
  (if (atom l) b (obag::insert (car l) (ins-all (cdr l) b))))

(defthm occs-ins-all
  (equal (obag::occs a (ins-all l b))
         (+ (occs-l a l) (obag::occs a b))))

(defthm bagp-ins-all
  (implies (obag::bagp b) (obag::bagp (ins-all l b))))

(defthm ins-all-insert
  (implies (obag::bagp b)
           (equal (ins-all l (obag::insert a b))
                  (obag::insert a (ins-all l b))))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm ins-all-commute
  (implies (obag::bagp x)
           (equal (ins-all a (ins-all b x))
                  (ins-all b (ins-all a x))))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm occs-l-append
  (equal (occs-l a (append x y)) (+ (occs-l a x) (occs-l a y))))

(defthm ins-all-append
  (equal (ins-all (append a b) x)
         (ins-all a (ins-all b x))))

;; ---------------------------------------------------------------
;; unit matrices
;; ---------------------------------------------------------------

(defun first-one (row)
  (cond ((atom row) 0)
        ((equal (car row) 1) 0)
        (t (1+ (first-one (cdr row))))))

(defun first-row (m)
  (cond ((atom m) 0)
        ((member-equal 1 (car m)) 0)
        (t (1+ (first-row (cdr m))))))

(defun ui (m) (first-row m))
(defun uj (m) (first-one (nth (first-row m) m)))

(defthm member-1-repeat-0
  (not (member-equal 1 (repeat n 0)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm member-1-bit-unit-list
  (implies (and (natp j) (< j (nfix n)))
           (member-equal 1 (bit-unit-list j n)))
  :hints (("Goal" :in-theory (enable bit-unit-list bit-listn0) :induct (ind-jn j n))))

(defthm first-one-bit-unit-list
  (implies (and (natp j) (< j (nfix n)))
           (equal (first-one (bit-unit-list j n)) j))
  :hints (("Goal" :in-theory (enable bit-unit-list bit-listn0) :induct (ind-jn j n))))

(defthm first-row-bit-mat-unit
  (implies (and (natp i) (< i (nfix m)) (natp j) (< j (nfix n)))
           (equal (first-row (bit-mat-unit i j m n)) i))
  :hints (("Goal" :in-theory (enable bit-mat-unit bit-mat0 bit-listn0) :induct (ind-jn i m))))

(defthm ui-uj-unit
  (implies (and (natp n) (natp i) (< i n) (natp j) (< j n))
           (and (equal (ui (bit-mat-unit i j n n)) i)
                (equal (uj (bit-mat-unit i j n n)) j))))

(in-theory (disable ui uj))

(defun unitp (m n)
  (and (natp (ui m)) (< (ui m) n) (natp (uj m)) (< (uj m) n)
       (equal m (bit-mat-unit (ui m) (uj m) n n))))

(defthm unitp-unit
  (implies (and (natp n) (natp i) (< i n) (natp j) (< j n))
           (unitp (bit-mat-unit i j n n) n)))

(defthm unitp-facts
  (implies (and (unitp m n) (natp n))
           (and (bit-matp m n n)
                (not (equal m (bit-mat0 n n)))))
  :hints (("Goal" :in-theory (disable unit-nonzero)
           :use ((:instance unit-nonzero (i (ui m)) (j (uj m)))))))

(in-theory (disable unitp))

(defun all-unitp (us n)
  (if (atom us) t (and (unitp (car us) n) (all-unitp (cdr us) n))))

(defthm all-unitp-append
  (equal (all-unitp (append a b) n) (and (all-unitp a n) (all-unitp b n))))

(defthm all-unitp-units-row
  (implies (and (natp n) (natp i) (< i n) (natp c) (<= c n))
           (all-unitp (units-row x i c n) n)))

(defthm all-unitp-units-rows
  (implies (and (natp n) (natp c) (<= c n))
           (all-unitp (units-rows x c n) n)))

(defthm all-unitp-all-matp
  (implies (and (all-unitp us n) (natp n)) (all-matp us n)))

;; ---------------------------------------------------------------
;; splitting one summand into pieces with unit p-component
;; ---------------------------------------------------------------

(defun split-moves (w p us k n)
  (declare (xargs :measure (len us)))
  (cond ((atom us) nil)
        ((equal (sget w p) (car us)) nil)
        (t (let* ((e (sset w p (car us)))
                  (w2 (sset w p (bit-mat-add (sget w p) (car us)))))
             (append (xpair-moves e k n)
                     (cons (mv-flip (pos-next p) w e)
                           (split-moves w2 p (cdr us) k n)))))))

(defun pieces (w p us)
  (declare (xargs :measure (len us)))
  (cond ((atom us) (list w))
        ((equal (sget w p) (car us)) (list w))
        (t (cons (sset w p (car us))
                 (pieces (sset w p (bit-mat-add (sget w p) (car us))) p (cdr us))))))

(defun split-ind (w p us b)
  (declare (xargs :measure (len us)))
  (cond ((atom us) b)
        ((equal (sget w p) (car us)) b)
        (t (let* ((e (sset w p (car us)))
                  (w2 (sset w p (bit-mat-add (sget w p) (car us)))))
             (split-ind w2 p (cdr us)
                        (obag::insert w2 (obag::insert e (obag::delete w b))))))))

(defthm summandp-sset-unit
  (implies (and (summandp w n) (posp3 p) (unitp e n) (natp n))
           (summandp (sset w p e) n)))

(defthm summandp-sset-add-unit
  (implies (and (summandp w n) (posp3 p) (unitp e n) (natp n)
                (not (equal (sget w p) e)))
           (summandp (sset w p (bit-mat-add (sget w p) e)) n))
  :hints (("Goal" :use ((:instance bit-mat-add-equal-zero (a (sget w p)) (b e) (m n))))))

(defthm split-moves-lemma
  (implies (and (correct-schemep k n) (natp n) (<= 2 n)
                (obag::bagp b) (summandp w n) (< 0 (obag::occs w b))
                (posp3 p) (all-unitp us n))
           (and (path-validp (split-moves w p us k n) (obag::sum k b) n)
                (equal (apply-moves (split-moves w p us k n) (obag::sum k b) n)
                       (obag::sum k (ins-all (pieces w p us) (obag::delete w b))))))
  :hints (("Goal" :induct (split-ind w p us b)
           :in-theory (e/d () (xpair-moves-lemma frame-lemma mv-flip)))
          ("Subgoal *1/3" :use ((:instance xpair-moves-lemma (s k) (x (sset w p (car us))))
                                (:instance frame-lemma (s k) (j b)
                                           (ms (xpair-moves (sset w p (car us)) k n)))))
          ))

;; split all elements of a list along p

(defun split-all-moves (l p k n)
  (if (atom l)
      nil
    (append (split-moves (car l) p (units-rows (sget (car l) p) n n) k n)
            (split-all-moves (cdr l) p k n))))

(defun pieces-all (l p n)
  (if (atom l)
      nil
    (append (pieces (car l) p (units-rows (sget (car l) p) n n))
            (pieces-all (cdr l) p n))))

(defun split-all-ind (l p n b0)
  (if (atom l)
      b0
    (split-all-ind (cdr l) p n (ins-all (pieces (car l) p (units-rows (sget (car l) p) n n)) b0))))

(defthm split-all-moves-lemma
  (implies (and (correct-schemep k n) (natp n) (<= 2 n)
                (obag::bagp b0) (all-summandp l n) (posp3 p))
           (and (path-validp (split-all-moves l p k n) (obag::sum k (ins-all l b0)) n)
                (equal (apply-moves (split-all-moves l p k n) (obag::sum k (ins-all l b0)) n)
                       (obag::sum k (ins-all (pieces-all l p n) b0)))))
  :hints (("Goal" :induct (split-all-ind l p n b0)
           :in-theory (e/d () (split-moves-lemma pieces split-moves)))
          ("Subgoal *1/2" :use ((:instance split-moves-lemma (w (car l))
                                           (us (units-rows (sget (car l) p) n n))
                                           (b (ins-all l b0)))))))

;;;; ================= from pred2 =================



;; ---------------------------------------------------------------
;; properties of pieces
;; ---------------------------------------------------------------

(defun all-unit-at (l p n)
  (if (atom l) t (and (unitp (sget (car l) p) n) (all-unit-at (cdr l) p n))))

(defthm all-unit-at-append
  (equal (all-unit-at (append a b) p n) (and (all-unit-at a p n) (all-unit-at b p n))))

(defthm all-summandp-append
  (equal (all-summandp (append a b) n) (and (all-summandp a n) (all-summandp b n))))

(defthm all-summandp-pieces
  (implies (and (summandp w n) (posp3 p) (all-unitp us n) (natp n))
           (all-summandp (pieces w p us) n)))

(defthm all-summandp-pieces-all
  (implies (and (all-summandp l n) (posp3 p) (natp n))
           (all-summandp (pieces-all l p n) n)))

(defthm pieces-unit-at-p
  (implies (and (summandp w n) (posp3 p) (all-unitp us n) (natp n)
                (equal (lsum us n) (sget w p)))
           (all-unit-at (pieces w p us) p n))
  :hints (("Goal" :induct (pieces w p us))))

(defthm pieces-unit-at-q
  (implies (and (posp3 p) (posp3 q) (not (equal p q))
                (unitp (sget w q) n))
           (all-unit-at (pieces w p us) q n)))

(defthm pieces-all-unit-at-p
  (implies (and (all-summandp l n) (posp3 p) (natp n))
           (all-unit-at (pieces-all l p n) p n)))

(defthm pieces-all-unit-at-q
  (implies (and (all-unit-at l q n) (posp3 p) (posp3 q) (not (equal p q)))
           (all-unit-at (pieces-all l p n) q n)))

;; tensor sums of pieces

(defthm all-summandp-all-dimp
  (implies (all-summandp l n) (all-dimp l n)))

(defthm scheme-sum-append
  (implies (and (natp n) (all-dimp a n) (all-dimp b n))
           (equal (scheme-sum (append a b) n)
                  (bit-list-add (scheme-sum a n) (scheme-sum b n))))
  :hints (("Goal" :in-theory (enable scheme-sum bit-listn0))))

(defthm scheme-sum-single
  (implies (and (natp n) (summand-dimp w n))
           (equal (scheme-sum (list w) n) (summand-tensor w)))
  :hints (("Goal" :in-theory (enable scheme-sum bit-listn0))))

(defthm scheme-sum-pieces
  (implies (and (summandp w n) (posp3 p) (all-unitp us n) (natp n))
           (equal (scheme-sum (pieces w p us) n) (summand-tensor w)))
  :hints (("Goal" :induct (pieces w p us)
           :in-theory (enable scheme-sum))
          ("Subgoal *1/3" :use ((:instance summand-tensor-sset-add
                                           (x (car us))
                                           (y (bit-mat-add (sget w p) (car us))))))))

(defthm scheme-sum-pieces-all
  (implies (and (all-summandp l n) (posp3 p) (natp n))
           (equal (scheme-sum (pieces-all l p n) n) (scheme-sum l n)))
  :hints (("Goal" :in-theory (e/d (scheme-sum) (pieces)))))

;; ---------------------------------------------------------------
;; unit triples and parity
;; ---------------------------------------------------------------

(defun all-utp (l n)
  (if (atom l)
      t
    (and (summandp (car l) n)
         (unitp (sget (car l) 0) n)
         (unitp (sget (car l) 1) n)
         (unitp (sget (car l) 2) n)
         (all-utp (cdr l) n))))

(defthm all-utp-from-parts
  (implies (and (all-summandp l n) (all-unit-at l 0 n) (all-unit-at l 1 n) (all-unit-at l 2 n))
           (all-utp l n)))

(defun coord (u n)
  (tidx (ui (sget u 0)) (uj (sget u 0))
        (ui (sget u 1)) (uj (sget u 1))
        (ui (sget u 2)) (uj (sget u 2)) n))

(defthm natp-coord
  (implies (natp n) (natp (coord u n)))
  :hints (("Goal" :in-theory (enable ui uj)))
  :rule-classes (:rewrite :type-prescription))

(defthm unit-entry-at-witness
  (implies (and (unitp a n) (unitp b n) (natp n))
           (equal (nth (uj a) (nth (ui a) b))
                  (if (equal a b) 1 0)))
  :hints (("Goal" :in-theory (enable unitp)
           :use ((:instance unit-injective (i (ui a)) (j (uj a)) (i2 (ui b)) (j2 (uj b)))))))

(defthm tco-coord-tensor
  (implies (and (summandp u n) (summandp v n) (natp n)
                (unitp (sget u 0) n) (unitp (sget u 1) n) (unitp (sget u 2) n)
                (unitp (sget v 0) n) (unitp (sget v 1) n) (unitp (sget v 2) n))
           (equal (tco (coord u n) (summand-tensor v))
                  (if (equal u v) 1 0)))
  :hints (("Goal" :in-theory (e/d (summand-tensor summand-get-pos summandp unitp) (tco unit-entry-at-witness))
           :use ((:instance unit-entry-at-witness (a (car u)) (b (car v)))
                 (:instance unit-entry-at-witness (a (cadr u)) (b (cadr v)))
                 (:instance unit-entry-at-witness (a (caddr u)) (b (caddr v)))
                 (:instance mat-triplep-shape (s u))
                 (:instance mat-triplep-shape (s v))))))

(defun cpar (u l)
  (if (atom l) 0 (bitxor (if (equal u (car l)) 1 0) (cpar u (cdr l)))))

(defthm xco-coord
  (implies (and (all-utp l n) (natp n) (summandp u n)
                (unitp (sget u 0) n) (unitp (sget u 1) n) (unitp (sget u 2) n))
           (equal (xco (coord u n) l) (cpar u l)))
  :hints (("Goal" :in-theory (e/d () (coord tco)))))

(defthm cpar-non-member
  (implies (not (member-equal u l)) (equal (cpar u l) 0)))

(defthm scheme-sum-remove1
  (implies (and (member-equal u l) (all-dimp l n) (natp n))
           (equal (scheme-sum l n)
                  (bit-list-add (summand-tensor u) (scheme-sum (remove1-equal u l) n))))
  :hints (("Goal" :in-theory (enable scheme-sum))))

(defthm all-utp-remove1
  (implies (all-utp l n) (all-utp (remove1-equal u l) n)))

(defthm all-utp-all-dimp
  (implies (all-utp l n) (all-dimp l n)))

(defthm len-remove1-equal
  (<= (len (remove1-equal a l)) (len l))
  :rule-classes :linear)

(defun cancel-moves (u)
  (declare (xargs :measure (len u)))
  (if (atom u)
      nil
    (cons (mv-flip 0 (car u) (car u))
          (cancel-moves (remove1-equal (car u) (cdr u))))))

(defun zeros6 (n) (repeat (* n n n n n n) 0))

(defthm zero-sum-member
  (implies (and (equal (scheme-sum l n) (zeros6 n))
                (consp l) (all-utp l n) (natp n))
           (member-equal (car l) (cdr l)))
  :hints (("Goal" :in-theory (e/d () (tco tco-scheme-sum xco-coord coord cpar-non-member))
           :use ((:instance tco-scheme-sum (k (coord (car l) n)))
                 (:instance xco-coord (u (car l)))
                 (:instance cpar-non-member (u (car l)) (l (cdr l)))))))

(defthm zero-sum-occs
  (implies (and (equal (scheme-sum l n) (zeros6 n))
                (consp l) (all-utp l n) (natp n))
           (< 0 (occs-l (car l) (cdr l))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance zero-sum-member)
                        (:instance occs-l-member (a (car l)) (s (cdr l))))
           :in-theory (disable zero-sum-member occs-l-member zeros6))))

(defthm zero-sum-rest
  (implies (and (consp l) (all-utp l n) (natp n)
                (equal (scheme-sum l n) (zeros6 n)))
           (equal (scheme-sum (remove1-equal (car l) (cdr l)) n) (zeros6 n)))
  :hints (("Goal" :in-theory (e/d (scheme-sum) (zero-sum-member scheme-sum-remove1))
           :use ((:instance zero-sum-member)
                 (:instance scheme-sum-remove1 (u (car l)) (l (cdr l)))))))

(defthm occs-l-remove1
  (equal (occs-l a (remove1-equal u l))
         (if (and (equal a u) (member-equal u l))
             (1- (occs-l a l))
           (occs-l a l))))

(defthm delete-ins-all
  (implies (and (member-equal u l) (obag::bagp b))
           (equal (obag::delete u (ins-all l b))
                  (ins-all (remove1-equal u l) b)))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite))))

(defthm cancel-moves-lemma
  (implies (and (obag::bagp k) (all-utp l n) (natp n)
                (equal (scheme-sum l n) (zeros6 n)))
           (and (path-validp (cancel-moves l) (obag::sum k (ins-all l nil)) n)
                (equal (apply-moves (cancel-moves l) (obag::sum k (ins-all l nil)) n)
                       k)))
  :hints (("Goal" :induct (cancel-moves l)
           :in-theory (e/d () (mv-flip zeros6)))
          ))

;; ---------------------------------------------------------------
;; reduction of a zero-sum list in a correct context
;; ---------------------------------------------------------------

(defun reduce-moves (m k n)
  (let* ((l1 (pieces-all m 0 n))
         (l2 (pieces-all l1 1 n))
         (l3 (pieces-all l2 2 n)))
    (append (split-all-moves m 0 k n)
            (append (split-all-moves l1 1 k n)
                    (append (split-all-moves l2 2 k n)
                            (cancel-moves l3))))))

(defthm reduce-moves-lemma
  (implies (and (correct-schemep k n) (natp n) (<= 2 n)
                (all-summandp m n)
                (equal (scheme-sum m n) (zeros6 n)))
           (and (path-validp (reduce-moves m k n) (obag::sum k (ins-all m nil)) n)
                (equal (apply-moves (reduce-moves m k n) (obag::sum k (ins-all m nil)) n)
                       k)))
  :hints (("Goal" :in-theory (e/d () (split-all-moves cancel-moves pieces-all zeros6
                                      split-all-moves-lemma cancel-moves-lemma))
           :use ((:instance split-all-moves-lemma (l m) (p 0) (b0 nil))
                 (:instance split-all-moves-lemma (l (pieces-all m 0 n)) (p 1) (b0 nil))
                 (:instance split-all-moves-lemma (l (pieces-all (pieces-all m 0 n) 1 n)) (p 2) (b0 nil))
                 (:instance cancel-moves-lemma
                            (l (pieces-all (pieces-all (pieces-all m 0 n) 1 n) 2 n)))))))

;;;; ================= from pmain1 =================



(defthm occs-dbl
  (equal (obag::occs a (dbl l)) (* 2 (occs-l a l))))

(defthm summand-listp-all-summandp
  (implies (summand-listp l n) (all-summandp l n)))

(defthm main1-state-eq
  (implies (and (obag::bagp s) (obag::bagp s2))
           (equal (obag::sum s (obag::sum (dbl s2) nil))
                  (obag::sum s2 (ins-all (append s s2) nil))))
  :hints (("Goal" :in-theory (enable bag-equal-rewrite obag-occs-is-occs-l))))

(defthm main1-zero-sum
  (implies (and (correct-schemep s n) (correct-schemep s2 n) (natp n))
           (equal (scheme-sum (append s s2) n) (zeros6 n)))
  :hints (("Goal" :in-theory (enable correct-schemep))))

(defun main1-moves (s s2 n)
  (append (addp-moves s2 s n)
          (reduce-moves (append s s2) s2 n)))

(defthm main1-moves-lemma
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (and (path-validp (main1-moves sch sch2 n) sch n)
                (equal (apply-moves (main1-moves sch sch2 n) sch n) sch2)))
  :hints (("Goal" :in-theory (e/d () (addp-moves reduce-moves addp-moves-lemma reduce-moves-lemma
                                     zeros6 main1-state-eq))
           :use ((:instance addp-moves-lemma (s sch) (l sch2) (j nil))
                 (:instance main1-state-eq (s sch) (s2 sch2))
                 (:instance reduce-moves-lemma (k sch2) (m (append sch sch2)))))))

(defthm main-1
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (flip-plus-reachablep sch sch2 n))
  :hints (("Goal" :use ((:instance flip-plus-reachablep-suff
                                   (moves (main1-moves sch sch2 n)))
                        (:instance main1-moves-lemma))
           :in-theory (disable flip-plus-reachablep-suff main1-moves-lemma main1-moves))))

;;;; ================= from palg1 =================



;; ---------------------------------------------------------------
;; linear forms and their matrices
;; ---------------------------------------------------------------

(defthm bit-list-p-scale-len
  (implies (bit-listnp x n) (bit-listnp (bit-list-scale c x) n)))

(defthm bit-matp-bit-mat-scale
  (implies (bit-matp a m n) (bit-matp (bit-mat-scale c a) m n))
  :hints (("Goal" :in-theory (enable bit-matp bit-mat-scale))))

(defthm bit-mat-scale-0
  (implies (bit-matp a m n) (equal (bit-mat-scale 0 a) (bit-mat0 m n)))
  :hints (("Goal" :in-theory (enable bit-matp bit-mat-scale bit-mat0 bit-listn0 repeat))))

(defthm bit-mat-scale-0-unit
  (equal (bit-mat-scale 0 (bit-mat-unit i j m n)) (bit-mat0 m n))
  :hints (("Goal" :use ((:instance bit-mat-scale-0 (a (bit-mat-unit i j m n)))))))

(defthm bit-matp-lform-mat
  (implies (natp n) (bit-matp (lform-mat e n) n n))
  :hints (("Goal" :in-theory (enable lform-mat))))

(defthm lform-mat-mat-lform-row
  (implies (and (bit-matp a n n) (natp n) (< 0 n) (natp i) (< i n) (natp c) (<= c n))
           (equal (lform-mat (mat-lform-row a i c n) n)
                  (lsum (units-row a i c n) n)))
  :hints (("Goal" :in-theory (enable mat-lform-row lform-mat))))

(defthm lform-mat-mat-lform-rows
  (implies (and (bit-matp a n n) (natp n) (< 0 n) (natp c) (<= c n))
           (equal (lform-mat (mat-lform-rows a c n) n)
                  (lsum (units-rows a c n) n)))
  :hints (("Goal" :in-theory (enable mat-lform-rows lform-mat))))

(defthm lform-mat-mat-lform
  (implies (and (bit-matp a n n) (natp n) (< 0 n))
           (equal (lform-mat (mat-lform a n) n) a))
  :hints (("Goal" :in-theory (enable mat-lform))))

(defthm lformp-mat-lform-row
  (implies (and (natp n) (< 0 n) (natp i) (< i n) (natp c) (<= c n))
           (lformp (mat-lform-row a i c n) n))
  :hints (("Goal" :in-theory (enable mat-lform-row lformp))))

(defthm lformp-mat-lform-rows
  (implies (and (natp n) (< 0 n) (natp c) (<= c n))
           (lformp (mat-lform-rows a c n) n))
  :hints (("Goal" :in-theory (enable mat-lform-rows lformp))))

(defthm lformp-mat-lform
  (implies (and (natp n) (< 0 n))
           (lformp (mat-lform a n) n))
  :hints (("Goal" :in-theory (enable mat-lform))))

;; ---------------------------------------------------------------
;; dot products
;; ---------------------------------------------------------------

(defun ldot (x y)
  (if (or (atom x) (atom y))
      0
    (bitxor (bitand (car x) (car y)) (ldot (cdr x) (cdr y)))))

(defthm bitp-ldot (bitp (ldot x y)))

(defthm ldot-append
  (implies (equal (len x1) (len y1))
           (equal (ldot (append x1 x2) (append y1 y2))
                  (bitxor (ldot x1 y1) (ldot x2 y2))))
  :hints (("Goal" :induct (ldot x1 y1))))

(defthm ldot-add
  (implies (and (bit-list-p x1) (bit-list-p x2) (bit-list-p y)
                (equal (len x1) (len x2)))
           (equal (ldot (bit-list-add x1 x2) y)
                  (bitxor (ldot x1 y) (ldot x2 y))))
  :hints (("Goal" :in-theory (enable bit-list-add bitand-bitxor-dist-2)
           :induct (list (bit-list-add x1 x2) (ldot x1 y)))))

(defthm ldot-scale
  (implies (and (bitp c) (bit-list-p x) (bit-list-p y))
           (equal (ldot (bit-list-scale c x) y)
                  (bitand c (ldot x y))))
  :hints (("Goal" :in-theory (enable bit-list-scale bitand-bitxor-dist)
           :induct (ldot x y))))

(defun ind-ky (k y) (if (zp k) y (ind-ky (1- k) (cdr y))))

(defthm ldot-repeat-0
  (equal (ldot (repeat k 0) y) 0)
  :hints (("Goal" :in-theory (enable repeat) :induct (ind-ky k y))))

(defthm ldot-bit-unit-list-0
  (implies (and (bit-list-p y) (natp j) (< j (len y)))
           (equal (ldot (bit-unit-list j (len y)) y) (nth j y)))
  :hints (("Goal" :in-theory (enable bit-unit-list bit-listn0) :induct (ind-ky j y))))

(defthm ldot-bit-unit-list
  (implies (and (bit-list-p y) (natp j) (< j (len y)) (equal (len y) n))
           (equal (ldot (bit-unit-list j n) y) (nth j y))))

(defun mdot (a d) (ldot (mat-flat a) (mat-flat d)))

(defun zl (x) (if (atom x) t (and (equal (car x) 0) (zl (cdr x)))))

(defthm ldot-zl (implies (zl x) (equal (ldot x y) 0)))

(defthm zl-append (implies (and (zl x) (zl y)) (zl (append x y))))

(defthm zl-repeat (zl (repeat n 0)) :hints (("Goal" :in-theory (enable repeat))))

(defthm zl-flat-mat0
  (implies (zl r) (zl (mat-flat (repeat m r))))
  :hints (("Goal" :in-theory (enable mat-flat repeat) :induct (repeat m r))))

(defthm mdot-mat0
  (equal (mdot (bit-mat0 m n) d) 0)
  :hints (("Goal" :in-theory (enable bit-mat0 bit-listn0))))

(defthm mdot-add
  (implies (and (bind-free (find-dim mfc state) (m n))
                (bit-matp a m n) (bit-matp b m n) (bit-list-listp d) (natp n))
           (equal (mdot (bit-mat-add a b) d)
                  (bitxor (mdot a d) (mdot b d)))))

(defthm scale-append
  (equal (bit-list-scale c (append x y))
         (append (bit-list-scale c x) (bit-list-scale c y)))
  :hints (("Goal" :in-theory (enable bit-list-scale))))

(defthm mat-flat-scale
  (equal (mat-flat (bit-mat-scale c a))
         (bit-list-scale c (mat-flat a)))
  :hints (("Goal" :in-theory (enable mat-flat bit-mat-scale bit-list-scale))))

(defthm bit-list-listp-scale
  (bit-list-listp (bit-mat-scale c a))
  :hints (("Goal" :in-theory (enable bit-mat-scale))))

(defthm mdot-scale
  (implies (and (bitp c) (bit-list-listp a) (bit-list-listp d))
           (equal (mdot (bit-mat-scale c a) d)
                  (bitand c (mdot a d)))))

(defthm mdot-unit
  (implies (and (bit-matp d m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
           (equal (mdot (bit-mat-unit i j m n) d)
                  (nth j (nth i d))))
  :hints (("Goal" :induct (ind-ami d m i)
           :in-theory (enable bit-matp mat-flat bit-mat-unit bit-mat0 bit-listn0)
           :expand ((bit-mat-unit i j m n) (mat-flat d) (bit-matp d m n)))))

(in-theory (disable mdot))

(defthm eval-lform-mdot
  (implies (and (lformp e n) (bit-matp d n n) (natp n))
           (equal (eval-lform e d n)
                  (mdot (lform-mat e n) d)))
  :hints (("Goal" :in-theory (enable eval-lform lform-mat lformp))))

;;;; ================= from palg2 =================



;; ---------------------------------------------------------------
;; structure of triples-outs
;; ---------------------------------------------------------------

(defthm nth-triples-outs-row
  (implies (and (natp l) (natp c) (< l c))
           (equal (nth l (triples-outs-row s k c n))
                  (c-indices s k (+ (- n c) l) 0)))
  :hints (("Goal" :in-theory (enable triples-outs-row nth) :induct (ind-jn l c)
           :expand ((triples-outs-row s k c n)))))

(defthm nth-triples-outs-rows
  (implies (and (natp k) (natp c) (< k c))
           (equal (nth k (triples-outs-rows s c n))
                  (triples-outs-row s (+ (- n c) k) n n)))
  :hints (("Goal" :in-theory (enable triples-outs-rows nth) :induct (ind-jn k c)
           :expand ((triples-outs-rows s c n)))))

(defthm len-triples-outs-row
  (equal (len (triples-outs-row s k c n)) (nfix c))
  :hints (("Goal" :in-theory (enable triples-outs-row))))

(defthm len-triples-outs-rows
  (equal (len (triples-outs-rows s c n)) (nfix c))
  :hints (("Goal" :in-theory (enable triples-outs-rows))))

(defthm nth-nth-triples-outs
  (implies (and (natp n) (natp k) (< k n) (natp l) (< l n))
           (equal (nth l (nth k (triples-outs s n)))
                  (c-indices s k l 0)))
  :hints (("Goal" :in-theory (enable triples-outs))))

;; c-mat

(defthm len-triples-outs
  (equal (len (triples-outs s n)) (nfix n))
  :hints (("Goal" :in-theory (enable triples-outs))))

(defthm len-nth-triples-outs
  (implies (and (natp n) (natp k) (< k n))
           (equal (len (nth k (triples-outs s n))) n))
  :hints (("Goal" :in-theory (enable triples-outs))))

(defthm len-c-mat-row
  (equal (len (c-mat-row r row)) (len row))
  :hints (("Goal" :in-theory (enable c-mat-row))))

(defthm len-c-mat
  (equal (len (c-mat r outs)) (len outs))
  :hints (("Goal" :in-theory (enable c-mat))))

(defthm nth-c-mat-row
  (implies (and (natp l) (< l (len row)))
           (equal (nth l (c-mat-row r row)) (occ-parity r (nth l row))))
  :hints (("Goal" :in-theory (enable c-mat-row nth))))

(defthm nth-c-mat
  (implies (and (natp k) (< k (len outs)))
           (equal (nth k (c-mat r outs)) (c-mat-row r (nth k outs))))
  :hints (("Goal" :in-theory (enable c-mat nth))))

(defthm bitp-occ-parity (bitp (occ-parity r idxs))
  :hints (("Goal" :in-theory (enable occ-parity))))

(defthm bit-list-p-c-mat-row (bit-list-p (c-mat-row r row))
  :hints (("Goal" :in-theory (enable c-mat-row))))

(defun all-len (outs n)
  (if (atom outs) (null outs) (and (equal (len (car outs)) n) (all-len (cdr outs) n))))

(defthm bit-matp-c-mat
  (implies (and (all-len outs n) (equal (len outs) m) (natp n))
           (bit-matp (c-mat r outs) m n))
  :hints (("Goal" :in-theory (enable c-mat bit-matp))))

(defthm all-len-triples-outs-rows
  (implies (natp n) (all-len (triples-outs-rows s c n) n))
  :hints (("Goal" :in-theory (enable triples-outs-rows))))

(defthm bit-matp-c-mat-triples-outs
  (implies (natp n) (bit-matp (c-mat r (triples-outs s n)) n n))
  :hints (("Goal" :in-theory (enable triples-outs))))

;; occ-parity of c-indices

(defthm occ-parity-c-indices
  (implies (and (natp r) (natp r0))
           (equal (occ-parity r (c-indices l k j r0))
                  (if (and (<= r0 r) (< r (+ r0 (len l)))
                           (equal (nth j (nth k (caddr (nth (- r r0) l)))) 1))
                      1 0)))
  :hints (("Goal" :in-theory (enable c-indices occ-parity nth)
           :induct (c-indices l k j r0))))

(defthm all-dimp-nth
  (implies (and (all-dimp s n) (natp r) (< r (len s)))
           (summand-dimp (nth r s) n))
  :hints (("Goal" :in-theory (enable nth))))

(defthm summand-dimp-parts
  (implies (summand-dimp x n)
           (and (mat-triplep x)
                (bit-matp (car x) n n) (bit-matp (cadr x) n n) (bit-matp (caddr x) n n)))
  :hints (("Goal" :in-theory (enable summand-dimp))))

(defthm c-mat-triples-outs
  (implies (and (all-dimp s n) (natp n) (natp r) (< r (len s)))
           (equal (c-mat r (triples-outs s n))
                  (caddr (nth r s))))
  :hints (("Goal" :in-theory (disable triples-outs) :do-not-induct t
           :use ((:instance mat-ext (a (c-mat r (triples-outs s n)))
                            (b (caddr (nth r s))) (m n))))))

;;;; ================= from palg3 =================



;; ---------------------------------------------------------------
;; MAIN-4
;; ---------------------------------------------------------------

(defthm nthcdr-plus-1
  (implies (natp r)
           (equal (nthcdr (+ 1 r) s) (cdr (nthcdr r s))))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-nil (equal (nthcdr r nil) nil)
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm consp-nthcdr-len
  (implies (and (natp r) (consp (nthcdr r s)))
           (< r (len s)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (ind-ky r s))))

(defthm car-nthcdr
  (equal (car (nthcdr r s)) (nth r s))
  :hints (("Goal" :in-theory (enable nthcdr nth))))

(defthm atom-nthcdr-true-listp
  (implies (and (true-listp s) (not (consp (nthcdr r s))))
           (equal (nthcdr r s) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm summand-dimp-shape
  (implies (summand-dimp x n)
           (equal (list (car x) (cadr x) (caddr x)) x))
  :hints (("Goal" :use ((:instance mat-triplep-shape (s x))))))

(defthm cons-nth-nthcdr
  (implies (consp (nthcdr r s))
           (equal (cons (nth r s) (cdr (nthcdr r s))) (nthcdr r s)))
  :hints (("Goal" :use ((:instance car-nthcdr)) :in-theory (disable car-nthcdr))))

(defun ind-tf (l r) (if (atom l) r (ind-tf (cdr l) (1+ r))))

(defthm triples-from-scheme
  (implies (and (all-dimp s n) (true-listp s) (natp n) (< 0 n) (natp r)
                (equal l (nthcdr r s)))
           (equal (triples-from (scheme-prods l n) (triples-outs s n) r n) l))
  :hints (("Goal" :induct (ind-tf l r)
           :in-theory (e/d (triples-from scheme-prods) (triples-outs)))
          ("Subgoal *1/2" :use ((:instance all-dimp-nth)
                                (:instance consp-nthcdr-len))
           :in-theory (e/d (triples-from scheme-prods) (triples-outs all-dimp-nth
                                                                     consp-nthcdr-len)))))

(defthm bagp-true-listp
  (implies (obag::bagp s) (true-listp s))
  :hints (("Goal" :in-theory (enable obag::bagp)))
  :rule-classes :forward-chaining)

(defthm insert-head-of-bag
  (implies (and (obag::bagp s) (consp s))
           (equal (obag::insert (car s) (cdr s)) s))
  :hints (("Goal" :in-theory (enable obag::insert obag::head obag::emptyp obag::bfix obag::bagp)
           :expand ((obag::insert (car s) (cdr s))))))

(defthm insert-all-nonzero-bag
  (implies (and (obag::bagp s) (summand-listp s n))
           (equal (insert-all-nonzero s nil n) s))
  :hints (("Goal" :induct (len s))))

(defthm main-4
  (implies (and (schemep sch n) (natp n) (< 0 n))
           (equal (algo-scheme (scheme-algo sch n) n) sch))
  :hints (("Goal" :in-theory (e/d (algo-scheme algo-triples scheme-algo)
                                  (triples-from-scheme insert-all-nonzero))
           :use ((:instance triples-from-scheme (s sch) (r 0) (l sch))
                 (:instance insert-all-nonzero-bag (s sch))))))

;;;; ================= from palg4 =================



;; ---------------------------------------------------------------
;; general formula for algorithm entries
;; ---------------------------------------------------------------

(defun psum (p idx r d f n)
  (if (atom p)
      0
    (bitxor (bitand (occ-parity r idx) (prod-value (car p) d f n))
            (psum (cdr p) idx (1+ r) d f n))))

(defthm bitp-prod-value (bitp (prod-value p d f n))
  :hints (("Goal" :in-theory (enable prod-value))))

(defthm occ-parity-cons
  (equal (occ-parity r (cons x rest))
         (bitxor (if (equal x r) 1 0) (occ-parity r rest)))
  :hints (("Goal" :in-theory (enable occ-parity))))

(defthm occ-parity-nil
  (equal (occ-parity r nil) 0)
  :hints (("Goal" :in-theory (enable occ-parity))))

(defun psum1 (p x r d f n)
  (if (atom p)
      0
    (bitxor (bitand (if (equal x r) 1 0) (prod-value (car p) d f n))
            (psum1 (cdr p) x (1+ r) d f n))))

(defthm psum-cons
  (equal (psum p (cons x rest) r d f n)
         (bitxor (psum1 p x r d f n) (psum p rest r d f n)))
  :hints (("Goal" :in-theory (enable bitand-bitxor-dist-2))))

(defthm psum1-value
  (implies (and (natp x) (natp r))
           (equal (psum1 p x r d f n)
                  (if (and (<= r x) (< x (+ r (len p))))
                      (prod-value (nth (- x r) p) d f n)
                    0)))
  :hints (("Goal" :in-theory (enable nth) :induct (psum1 p x r d f n))))

(defthm psum-nil
  (equal (psum p nil r d f n) 0))

(defthm prods-xor-psum
  (implies (index-listp idx (len p))
           (equal (prods-xor idx p d f n)
                  (psum p idx 0 d f n)))
  :hints (("Goal" :in-theory (enable prods-xor index-listp)
           :induct (prods-xor idx p d f n))))

(defun gsum (l d f k j)
  (if (atom l)
      0
    (bitxor (bitand (nth j (nth k (caddr (car l))))
                    (bitand (mdot (car (car l)) d) (mdot (cadr (car l)) f)))
            (gsum (cdr l) d f k j))))

(defthm prodp-parts
  (implies (prodp p n)
           (and (lformp (cadr p) n) (lformp (caddr p) n)))
  :hints (("Goal" :in-theory (enable prodp))))

(defthm gsum-triples-from
  (implies (and (prod-listp p n) (natp n) (bit-matp d n n) (bit-matp f n n)
                (natp k) (< k (len outs)) (natp j) (< j (len (nth k outs))))
           (equal (gsum (triples-from p outs r n) d f k j)
                  (psum p (nth j (nth k outs)) r d f n)))
  :hints (("Goal" :in-theory (enable triples-from prod-listp prod-value bitand-commutative)
           :induct (triples-from p outs r n))))

;; outs-rowsp facts

(defun ind-jnx (j n x)
  (if (zp j) (list n x) (ind-jnx (1- j) (1- n) (cdr x))))

(defthm len-outs-rowp
  (implies (and (outs-rowp row r n) (natp n)) (equal (len row) n))
  :hints (("Goal" :in-theory (enable outs-rowp))))

(defthm nth-outs-rowp
  (implies (and (outs-rowp row r n) (natp n) (natp j) (< j n))
           (index-listp (nth j row) r))
  :hints (("Goal" :in-theory (enable outs-rowp nth) :induct (ind-jnx j n row))))

(defthm outs-rowp-facts
  (implies (and (outs-rowp row r n) (natp n) (natp j) (< j n))
           (and (equal (len row) n)
                (index-listp (nth j row) r))))

(defthm len-outs-rowsp
  (implies (and (outs-rowsp outs r m n) (natp m)) (equal (len outs) m))
  :hints (("Goal" :in-theory (enable outs-rowsp))))

(defthm nth-outs-rowsp
  (implies (and (outs-rowsp outs r m n) (natp m) (natp k) (< k m))
           (outs-rowp (nth k outs) r n))
  :hints (("Goal" :in-theory (enable outs-rowsp nth) :induct (ind-jnx k m outs))))

(defthm outs-rowsp-facts
  (implies (and (outs-rowsp outs r m n) (natp m) (natp k) (< k m))
           (and (equal (len outs) m)
                (outs-rowp (nth k outs) r n))))

(defthm algo-entry-gsum
  (implies (and (algop alg n) (natp n) (bit-matp d n n) (bit-matp f n n)
                (natp k) (< k n) (natp j) (< j n))
           (equal (algo-entry alg d f k j n)
                  (gsum (algo-triples alg n) d f k j)))
  :hints (("Goal" :in-theory (e/d (algo-entry algo-triples algop) (outs-rowsp-facts outs-rowp-facts))
           :use ((:instance outs-rowsp-facts (outs (cdr alg)) (r (len (car alg))) (m n))
                 (:instance outs-rowp-facts (row (nth k (cdr alg))) (r (len (car alg))))))))

;; ---------------------------------------------------------------
;; entries of eval-algo and bit-mat-mul
;; ---------------------------------------------------------------

(defthm nth-eval-algo-row
  (implies (and (natp l) (natp c) (< l c))
           (equal (nth l (eval-algo-row alg d f k c n))
                  (algo-entry alg d f k (+ (- n c) l) n)))
  :hints (("Goal" :in-theory (enable eval-algo-row nth) :induct (ind-jn l c)
           :expand ((eval-algo-row alg d f k c n)))))

(defthm nth-eval-algo-rows
  (implies (and (natp k) (natp c) (< k c))
           (equal (nth k (eval-algo-rows alg d f c n))
                  (eval-algo-row alg d f (+ (- n c) k) n n)))
  :hints (("Goal" :in-theory (enable eval-algo-rows nth) :induct (ind-jn k c)
           :expand ((eval-algo-rows alg d f c n)))))

(defthm nth-bit-mat-mul-row
  (implies (and (natp l) (natp c) (< l c))
           (equal (nth l (bit-mat-mul-row d f k c n))
                  (mat-mul-entry d f k (+ (- n c) l) n n)))
  :hints (("Goal" :in-theory (enable bit-mat-mul-row nth) :induct (ind-jn l c)
           :expand ((bit-mat-mul-row d f k c n)))))

(defthm nth-bit-mat-mul-rows
  (implies (and (natp k) (natp c) (< k c))
           (equal (nth k (bit-mat-mul-rows d f c n))
                  (bit-mat-mul-row d f (+ (- n c) k) n n)))
  :hints (("Goal" :in-theory (enable bit-mat-mul-rows nth) :induct (ind-jn k c)
           :expand ((bit-mat-mul-rows d f c n)))))

(defthm entry-eval-algo
  (implies (and (natp n) (natp k) (< k n) (natp l) (< l n))
           (equal (nth l (nth k (eval-algo alg d f n)))
                  (algo-entry alg d f k l n)))
  :hints (("Goal" :in-theory (enable eval-algo))))

(defthm entry-bit-mat-mul
  (implies (and (natp n) (natp k) (< k n) (natp l) (< l n))
           (equal (nth l (nth k (bit-mat-mul d f n)))
                  (mat-mul-entry d f k l n n)))
  :hints (("Goal" :in-theory (enable bit-mat-mul))))

;; ---------------------------------------------------------------
;; values at unit matrices
;; ---------------------------------------------------------------

(defthm ldot-comm
  (equal (ldot x y) (ldot y x)))

(defthm mdot-unit-right
  (implies (and (bit-matp a m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
           (equal (mdot a (bit-mat-unit i j m n))
                  (nth j (nth i a))))
  :hints (("Goal" :in-theory (e/d (mdot) (mdot-unit ldot))
           :use ((:instance mdot-unit (d a))))))

(defthm gsum-units
  (implies (and (all-dimp l n) (natp n)
                (natp i1) (< i1 n) (natp j1) (< j1 n)
                (natp i2) (< i2 n) (natp j2) (< j2 n)
                (natp k) (< k n) (natp j) (< j n))
           (equal (gsum l (bit-mat-unit i1 j1 n n) (bit-mat-unit i2 j2 n n) k j)
                  (xco (tidx i1 j1 i2 j2 k j n) l)))
  :hints (("Goal" :in-theory (e/d (summand-tensor bitand-commutative bitand-commutative-2) (tco ldot-comm)))))

(defthm mat-mul-entry-units
  (implies (and (natp n)
                (natp i1) (< i1 n) (natp j1) (< j1 n)
                (natp i2) (< i2 n) (natp j2) (< j2 n)
                (natp k) (< k n) (natp l) (< l n) (natp h) (<= h n))
           (equal (mat-mul-entry (bit-mat-unit i1 j1 n n) (bit-mat-unit i2 j2 n n) k l h n)
                  (if (and (equal k i1) (equal j1 i2) (equal l j2) (< j1 h)) 1 0)))
  :hints (("Goal" :in-theory (enable mat-mul-entry) :induct (mat-mul-entry d f k l h n))))

;;;; ================= from pext =================



;; ---------------------------------------------------------------
;; tensor extensionality
;; ---------------------------------------------------------------

(defun qd (k n)
  (declare (xargs :measure (nfix k)))
  (if (or (zp n) (not (natp k)) (< k n)) 0 (1+ (qd (- k n) n))))

(defun rd (k n)
  (declare (xargs :measure (nfix k)))
  (if (or (zp n) (not (natp k)) (< k n)) k (rd (- k n) n)))

(defthm qd-rd-facts
  (implies (and (natp k) (posp n))
           (and (natp (qd k n)) (natp (rd k n))
                (< (rd k n) n)
                (equal (+ (* n (qd k n)) (rd k n)) k)))
  :rule-classes nil)

(defun ind-qa (k n a)
  (declare (xargs :measure (nfix k)))
  (if (or (zp n) (not (natp k)) (< k n)) a (ind-qa (- k n) n (1- a))))

(defthm qd-bound
  (implies (and (natp k) (posp n) (natp a) (< k (* a n)))
           (< (qd k n) a))
  :rule-classes nil
  :hints (("Goal" :induct (ind-qa k n a))
          ("Subgoal *1/2" :use ((:instance (:theorem (implies (and (natp a) (natp n) (< k (* a n)) (<= n k))
                                                              (< (- k n) (* (- a 1) n)))))))))

(defun bl-diff (x y)
  (cond ((atom x) 0)
        ((atom y) 0)
        ((equal (car x) (car y)) (1+ (bl-diff (cdr x) (cdr y))))
        (t 0)))

(defthm bl-diff-lemma
  (implies (and (true-listp x) (true-listp y) (equal (len x) (len y))
                (not (equal x y)))
           (and (< (bl-diff x y) (len x))
                (not (equal (nth (bl-diff x y) x) (nth (bl-diff x y) y)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nth))))

(defun digits (k n)
  (let* ((q1 (qd k n)) (d0 (rd k n))
         (q2 (qd q1 n)) (d1 (rd q1 n))
         (q3 (qd q2 n)) (d2 (rd q2 n))
         (q4 (qd q3 n)) (d3 (rd q3 n))
         (q5 (qd q4 n)) (d4 (rd q4 n)))
    (list q5 d4 d3 d2 d1 d0)))

(defthm digits-lemma
  (implies (and (natp k) (posp n) (< k (* n n n n n n)))
           (let ((ds (digits k n)))
             (and (natp (nth 0 ds)) (< (nth 0 ds) n)
                  (natp (nth 1 ds)) (< (nth 1 ds) n)
                  (natp (nth 2 ds)) (< (nth 2 ds) n)
                  (natp (nth 3 ds)) (< (nth 3 ds) n)
                  (natp (nth 4 ds)) (< (nth 4 ds) n)
                  (natp (nth 5 ds)) (< (nth 5 ds) n)
                  (equal (tidx (nth 0 ds) (nth 1 ds) (nth 2 ds) (nth 3 ds) (nth 4 ds) (nth 5 ds) n)
                         k))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable tidx)
           :use ((:instance qd-rd-facts)
                 (:instance qd-rd-facts (k (qd k n)))
                 (:instance qd-rd-facts (k (qd (qd k n) n)))
                 (:instance qd-rd-facts (k (qd (qd (qd k n) n) n)))
                 (:instance qd-rd-facts (k (qd (qd (qd (qd k n) n) n) n)))
                 (:instance qd-bound (a (* n n n n n)))
                 (:instance qd-bound (k (qd k n)) (a (* n n n n)))
                 (:instance qd-bound (k (qd (qd k n) n)) (a (* n n n)))
                 (:instance qd-bound (k (qd (qd (qd k n) n) n)) (a (* n n)))
                 (:instance qd-bound (k (qd (qd (qd (qd k n) n) n) n)) (a n))))))

(defthm tco-is-nth-for-bits
  (implies (and (bit-list-p x) (natp k) (< k (len x)))
           (equal (tco k x) (nth k x)))
  :hints (("Goal" :use ((:instance bitp-nth-bit-list (j k))) :in-theory (disable bitp-nth-bit-list))))

(defthm tensor-ext
  (implies (and (posp n) (bit-list-p x) (bit-list-p y)
                (equal (len x) (* n n n n n n)) (equal (len y) (len x))
                (not (equal x y)))
           (let ((ds (digits (bl-diff x y) n)))
             (and (natp (nth 0 ds)) (< (nth 0 ds) n)
                  (natp (nth 1 ds)) (< (nth 1 ds) n)
                  (natp (nth 2 ds)) (< (nth 2 ds) n)
                  (natp (nth 3 ds)) (< (nth 3 ds) n)
                  (natp (nth 4 ds)) (< (nth 4 ds) n)
                  (natp (nth 5 ds)) (< (nth 5 ds) n)
                  (not (equal (tco (tidx (nth 0 ds) (nth 1 ds) (nth 2 ds) (nth 3 ds) (nth 4 ds) (nth 5 ds) n) x)
                              (tco (tidx (nth 0 ds) (nth 1 ds) (nth 2 ds) (nth 3 ds) (nth 4 ds) (nth 5 ds) n) y))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable digits tco nth tidx)
           :use ((:instance bl-diff-lemma)
                 (:instance digits-lemma (k (bl-diff x y)))
                 (:instance tco-is-nth-for-bits (k (bl-diff x y)))
                 (:instance tco-is-nth-for-bits (k (bl-diff x y)) (x y))))))

(in-theory (disable digits))

;;;; ================= from pmain2 =================



;; ---------------------------------------------------------------
;; scheme-sum over bags built with insert
;; ---------------------------------------------------------------

(defthm scheme-sum-insert
  (implies (obag::bagp b)
           (equal (scheme-sum (obag::insert x b) n)
                  (bit-list-add (summand-tensor x) (scheme-sum b n))))
  :hints (("Goal" :in-theory (enable obag::insert obag::head obag::tail obag::emptyp
                                     obag::bfix scheme-sum)
           :induct (len b)
           :expand ((obag::insert x b)))))

(defthm zl-scale
  (implies (zl v) (zl (bit-list-scale b v)))
  :hints (("Goal" :in-theory (enable bit-list-scale))))

(defthm zl-scale-0
  (zl (bit-list-scale 0 v)))

(defthm zl-outer-left
  (implies (zl u) (zl (bit-list-outer u v)))
  :hints (("Goal" :in-theory (enable bit-list-outer))))

(defthm zl-outer-right
  (implies (zl v) (zl (bit-list-outer u v)))
  :hints (("Goal" :in-theory (enable bit-list-outer))))

(defthm zl-is-repeat
  (implies (and (zl x) (true-listp x))
           (equal x (repeat (len x) 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable repeat))))

(defthm zl-flat-bit-mat0
  (zl (mat-flat (bit-mat0 m n)))
  :hints (("Goal" :in-theory (enable bit-mat0 bit-listn0))))

(defthm zero-summand-tensor
  (implies (and (summand0p x n) (summand-dimp x n) (natp n))
           (equal (summand-tensor x) (repeat (* n n n n n n) 0)))
  :hints (("Goal" :in-theory (e/d (summand0p summand-tensor tensor summand-dimp) ())
           :use ((:instance zl-is-repeat (x (summand-tensor x)))))))

(defthm scheme-sum-insert-all-nonzero
  (implies (and (all-dimp l n) (natp n))
           (equal (scheme-sum (insert-all-nonzero l nil n) n)
                  (scheme-sum l n)))
  :hints (("Goal" :in-theory (enable scheme-sum)
           :induct (len l))))

;; summand-listp of the bag

(defthm summand-listp-insert
  (implies (and (obag::bagp b) (summandp x n) (summand-listp b n))
           (summand-listp (obag::insert x b) n))
  :hints (("Goal" :in-theory (enable obag::insert obag::head obag::tail obag::emptyp obag::bfix)
           :induct (len b)
           :expand ((obag::insert x b)))))

(defthm summandp-from-dimp
  (implies (and (summand-dimp x n) (not (summand0p x n)))
           (summandp x n))
  :hints (("Goal" :in-theory (enable summand-dimp summandp))))

(defthm bagp-insert-all-nonzero
  (implies (obag::bagp b) (obag::bagp (insert-all-nonzero l b n))))

(defthm summand-listp-insert-all-nonzero
  (implies (and (all-dimp l n) (obag::bagp b) (summand-listp b n))
           (summand-listp (insert-all-nonzero l b n) n))
  :hints (("Goal" :induct (len l))))

;; dimensions of algo-triples

(defthm outs-rowsp-all-len
  (implies (and (outs-rowsp outs r m n) (natp n))
           (all-len outs n))
  :hints (("Goal" :in-theory (enable outs-rowsp))))

(defthm all-dimp-triples-from
  (implies (and (natp n) (all-len outs n) (equal (len outs) n))
           (all-dimp (triples-from p outs r n) n))
  :hints (("Goal" :in-theory (enable triples-from summand-dimp))))

(defthm all-dimp-algo-triples
  (implies (and (algop alg n) (natp n))
           (all-dimp (algo-triples alg n) n))
  :hints (("Goal" :in-theory (enable algo-triples algop))))

;; ---------------------------------------------------------------
;; coefficients
;; ---------------------------------------------------------------

(defthm algo-coef
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n)
                (natp i1) (< i1 n) (natp j1) (< j1 n)
                (natp i2) (< i2 n) (natp j2) (< j2 n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (tco (tidx i1 j1 i2 j2 k l n) (scheme-sum (algo-triples alg n) n))
                  (tco (tidx i1 j1 i2 j2 k l n) (mm-tensor n))))
  :hints (("Goal" :in-theory (e/d () (tco algo-correctp algo-correctp-necc entry-eval-algo
                                          entry-bit-mat-mul eval-algo bit-mat-mul))
           :use ((:instance algo-correctp-necc (d (bit-mat-unit i1 j1 n n))
                            (f (bit-mat-unit i2 j2 n n)))
                 (:instance entry-eval-algo (d (bit-mat-unit i1 j1 n n))
                            (f (bit-mat-unit i2 j2 n n)))
                 (:instance entry-bit-mat-mul (d (bit-mat-unit i1 j1 n n))
                            (f (bit-mat-unit i2 j2 n n)))))))

(defthm len-mm-tensor
  (implies (natp n) (equal (len (mm-tensor n)) (* n n n n n n)))
  :hints (("Goal" :in-theory (enable mm-tensor))))

(defthm bit-list-p-mm-tensor
  (bit-list-p (mm-tensor n))
  :hints (("Goal" :in-theory (enable mm-tensor))))

(defthm algo-scheme-sum
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (equal (scheme-sum (algo-triples alg n) n) (mm-tensor n)))
  :hints (("Goal" :in-theory (e/d () (tco algo-correctp algo-coef nth))
           :use ((:instance tensor-ext (x (scheme-sum (algo-triples alg n) n))
                            (y (mm-tensor n)))
                 (:instance algo-coef
                            (i1 (nth 0 (digits (bl-diff (scheme-sum (algo-triples alg n) n) (mm-tensor n)) n)))
                            (j1 (nth 1 (digits (bl-diff (scheme-sum (algo-triples alg n) n) (mm-tensor n)) n)))
                            (i2 (nth 2 (digits (bl-diff (scheme-sum (algo-triples alg n) n) (mm-tensor n)) n)))
                            (j2 (nth 3 (digits (bl-diff (scheme-sum (algo-triples alg n) n) (mm-tensor n)) n)))
                            (k (nth 4 (digits (bl-diff (scheme-sum (algo-triples alg n) n) (mm-tensor n)) n)))
                            (l (nth 5 (digits (bl-diff (scheme-sum (algo-triples alg n) n) (mm-tensor n)) n))))))))

(defthm main-2
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (correct-schemep (algo-scheme alg n) n))
  :hints (("Goal" :in-theory (e/d (correct-schemep algo-scheme) (algo-correctp insert-all-nonzero)))))

;;;; ================= from pmain3 =================



;; ---------------------------------------------------------------
;; scheme-algo is an algorithm
;; ---------------------------------------------------------------

(defthm index-listp-c-indices
  (implies (natp r)
           (index-listp (c-indices l k j r) (+ r (len l))))
  :hints (("Goal" :in-theory (enable c-indices index-listp))))

(defthm index-listp-c-indices-0
  (index-listp (c-indices l k j 0) (len l))
  :hints (("Goal" :use ((:instance index-listp-c-indices (r 0))))))

(defthm outs-rowp-triples-outs-row
  (implies (natp c)
           (outs-rowp (triples-outs-row s k c n) (len s) c))
  :hints (("Goal" :in-theory (enable triples-outs-row outs-rowp))))

(defthm outs-rowsp-triples-outs-rows
  (implies (and (natp c) (natp n))
           (outs-rowsp (triples-outs-rows s c n) (len s) c n))
  :hints (("Goal" :in-theory (enable triples-outs-rows outs-rowsp))))

(defthm len-scheme-prods
  (equal (len (scheme-prods l n)) (len l))
  :hints (("Goal" :in-theory (enable scheme-prods))))

(defthm prod-listp-scheme-prods
  (implies (and (natp n) (< 0 n) (true-listp l))
           (prod-listp (scheme-prods l n) n))
  :hints (("Goal" :in-theory (enable scheme-prods prod-listp prodp))))

(defthm algop-scheme-algo
  (implies (and (natp n) (< 0 n) (true-listp s))
           (algop (scheme-algo s n) n))
  :hints (("Goal" :in-theory (enable algop scheme-algo triples-outs))))

(defthm algo-triples-scheme-algo
  (implies (and (all-dimp s n) (true-listp s) (natp n) (< 0 n))
           (equal (algo-triples (scheme-algo s n) n) s))
  :hints (("Goal" :in-theory (e/d (algo-triples scheme-algo) (triples-from-scheme))
           :use ((:instance triples-from-scheme (r 0) (l s))))))

;; ---------------------------------------------------------------
;; bilinearity
;; ---------------------------------------------------------------

(defthm mdot-comm
  (equal (mdot a d) (mdot d a))
  :hints (("Goal" :in-theory (enable mdot)))
  :rule-classes nil)

(defthm mdot-add-right
  (implies (and (bit-matp d1 n n) (bit-matp d2 n n) (bit-list-listp a) (natp n))
           (equal (mdot a (bit-mat-add d1 d2))
                  (bitxor (mdot a d1) (mdot a d2))))
  :hints (("Goal" :use ((:instance mdot-comm (d (bit-mat-add d1 d2)))
                        (:instance mdot-comm (d d1))
                        (:instance mdot-comm (d d2))))))

(defthm mdot-mat0-right
  (equal (mdot a (bit-mat0 m n)) 0)
  :hints (("Goal" :use ((:instance mdot-comm (d (bit-mat0 m n)))))))

(defthm bitp-mdot (bitp (mdot a d)) :hints (("Goal" :in-theory (enable mdot))))

(defthm gsum-add-d
  (implies (and (bind-free (find-n mfc state) (n))
                (all-dimp l n) (natp n) (bit-matp d1 n n) (bit-matp d2 n n)
                (natp k) (< k n) (natp j) (< j n))
           (equal (gsum l (bit-mat-add d1 d2) f k j)
                  (bitxor (gsum l d1 f k j) (gsum l d2 f k j))))
  :hints (("Goal" :in-theory (enable bitand-bitxor-dist bitand-bitxor-dist-2 summand-dimp))))

(defthm gsum-add-f
  (implies (and (bind-free (find-n mfc state) (n))
                (all-dimp l n) (natp n) (bit-matp f1 n n) (bit-matp f2 n n)
                (natp k) (< k n) (natp j) (< j n))
           (equal (gsum l d (bit-mat-add f1 f2) k j)
                  (bitxor (gsum l d f1 k j) (gsum l d f2 k j))))
  :hints (("Goal" :in-theory (enable bitand-bitxor-dist bitand-bitxor-dist-2 summand-dimp))))

(defthm gsum-zero-d
  (equal (gsum l (bit-mat0 n n) f k j) 0))

(defthm gsum-zero-f
  (equal (gsum l d (bit-mat0 n n) k j) 0))

(defthm mme-add-d
  (implies (and (natp n) (bit-matp d1 n n) (bit-matp d2 n n) (bit-matp f n n)
                (natp k) (< k n) (natp l) (< l n) (natp h) (<= h n))
           (equal (mat-mul-entry (bit-mat-add d1 d2) f k l h n)
                  (bitxor (mat-mul-entry d1 f k l h n) (mat-mul-entry d2 f k l h n))))
  :hints (("Goal" :in-theory (enable mat-mul-entry bitand-bitxor-dist bitand-bitxor-dist-2)
           :induct (mat-mul-entry d1 f k l h n))))

(defthm mme-add-f
  (implies (and (natp n) (bit-matp d n n) (bit-matp f1 n n) (bit-matp f2 n n)
                (natp k) (< k n) (natp l) (< l n) (natp h) (<= h n))
           (equal (mat-mul-entry d (bit-mat-add f1 f2) k l h n)
                  (bitxor (mat-mul-entry d f1 k l h n) (mat-mul-entry d f2 k l h n))))
  :hints (("Goal" :in-theory (enable mat-mul-entry bitand-bitxor-dist bitand-bitxor-dist-2)
           :induct (mat-mul-entry d f1 k l h n))))

(defthm mme-zero-d
  (implies (and (natp n) (natp k) (< k n) (natp l) (< l n) (natp h) (<= h n))
           (equal (mat-mul-entry (bit-mat0 n n) f k l h n) 0))
  :hints (("Goal" :in-theory (enable mat-mul-entry) :induct (mat-mul-entry d f k l h n))))

(defthm mme-zero-f
  (implies (and (natp n) (natp k) (< k n) (natp l) (< l n) (natp h) (<= h n))
           (equal (mat-mul-entry d (bit-mat0 n n) k l h n) 0))
  :hints (("Goal" :in-theory (enable mat-mul-entry) :induct (mat-mul-entry d f k l h n))))

;; ---------------------------------------------------------------
;; reduction to unit matrices
;; ---------------------------------------------------------------

(defthm unit-pair-eq0
  (implies (and (correct-schemep s n) (natp n)
                (natp i1) (< i1 n) (natp j1) (< j1 n)
                (natp i2) (< i2 n) (natp j2) (< j2 n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (gsum s (bit-mat-unit i1 j1 n n) (bit-mat-unit i2 j2 n n) k l)
                  (mat-mul-entry (bit-mat-unit i1 j1 n n) (bit-mat-unit i2 j2 n n) k l n n)))
  :hints (("Goal" :in-theory (e/d () (gsum mat-mul-entry tidx correct-schemep)))))

(defun gsum-mme-diff (s u v k l n)
  (equal (gsum s u v k l) (mat-mul-entry u v k l n n)))

(defthm unit-pair-eq
  (implies (and (correct-schemep s n) (natp n) (unitp u n) (unitp v n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (gsum s u v k l) (mat-mul-entry u v k l n n)))
  :hints (("Goal" :in-theory (e/d (unitp) (gsum mat-mul-entry tidx correct-schemep unit-pair-eq0))
           :use ((:instance unit-pair-eq0 (i1 (ui u)) (j1 (uj u)) (i2 (ui v)) (j2 (uj v)))))
          (and stable-under-simplificationp
               '(:use ((:instance (:theorem (implies (and (equal u x) (equal v y)
                                                          (gsum-mme-diff s x y k l n))
                                                     (gsum-mme-diff s u v k l n)))
                                  (x (bit-mat-unit (ui u) (uj u) n n))
                                  (y (bit-mat-unit (ui v) (uj v) n n))))))))

(defthm unit-left-eq
  (implies (and (correct-schemep s n) (natp n) (unitp u n) (all-unitp vs n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (gsum s u (lsum vs n) k l) (mat-mul-entry u (lsum vs n) k l n n)))
  :hints (("Goal" :in-theory (e/d () (gsum mat-mul-entry correct-schemep unit-pair-eq))
           :induct (len vs))
          ("Subgoal *1/1" :use ((:instance unit-pair-eq (v (car vs)))))))

(defthm unit-left-eq-2
  (implies (and (correct-schemep s n) (natp n) (unitp u n) (bit-matp f n n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (gsum s u f k l) (mat-mul-entry u f k l n n)))
  :hints (("Goal" :in-theory (e/d () (gsum mat-mul-entry correct-schemep unit-left-eq lsum-units-rows))
           :use ((:instance unit-left-eq (vs (units-rows f n n)))
                 (:instance lsum-units-rows (x f))))))

(defthm all-unit-eq
  (implies (and (correct-schemep s n) (natp n) (all-unitp us n) (bit-matp f n n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (gsum s (lsum us n) f k l) (mat-mul-entry (lsum us n) f k l n n)))
  :hints (("Goal" :in-theory (e/d () (gsum mat-mul-entry correct-schemep unit-left-eq-2))
           :induct (len us))
          ("Subgoal *1/1" :use ((:instance unit-left-eq-2 (u (car us)))))))

(defthm gsum-eq-mme
  (implies (and (correct-schemep s n) (natp n) (bit-matp d n n) (bit-matp f n n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (gsum s d f k l) (mat-mul-entry d f k l n n)))
  :hints (("Goal" :in-theory (e/d () (gsum mat-mul-entry correct-schemep all-unit-eq lsum-units-rows))
           :use ((:instance all-unit-eq (us (units-rows d n n)))
                 (:instance lsum-units-rows (x d))))))

;; ---------------------------------------------------------------
;; MAIN-3
;; ---------------------------------------------------------------

(defthm correct-schemep-true-listp
  (implies (correct-schemep s n) (true-listp s))
  :hints (("Goal" :in-theory (enable correct-schemep))))

(defthm scheme-algo-entry
  (implies (and (correct-schemep s n) (natp n) (< 0 n) (bit-matp d n n) (bit-matp f n n)
                (natp k) (< k n) (natp l) (< l n))
           (equal (algo-entry (scheme-algo s n) d f k l n)
                  (mat-mul-entry d f k l n n)))
  :hints (("Goal" :in-theory (e/d () (gsum mat-mul-entry correct-schemep algo-entry scheme-algo
                                          algo-entry-gsum algop-scheme-algo algo-triples-scheme-algo))
           :use ((:instance algo-entry-gsum (alg (scheme-algo s n)) (j l))
                 (:instance algop-scheme-algo)
                 (:instance algo-triples-scheme-algo)))))

(defthm scheme-algo-row
  (implies (and (correct-schemep s n) (natp n) (< 0 n) (bit-matp d n n) (bit-matp f n n)
                (natp k) (< k n) (natp c) (<= c n))
           (equal (eval-algo-row (scheme-algo s n) d f k c n)
                  (bit-mat-mul-row d f k c n)))
  :hints (("Goal" :in-theory (e/d (eval-algo-row bit-mat-mul-row)
                                  (gsum mat-mul-entry correct-schemep algo-entry scheme-algo)))))

(defthm scheme-algo-rows
  (implies (and (correct-schemep s n) (natp n) (< 0 n) (bit-matp d n n) (bit-matp f n n)
                (natp c) (<= c n))
           (equal (eval-algo-rows (scheme-algo s n) d f c n)
                  (bit-mat-mul-rows d f c n)))
  :hints (("Goal" :in-theory (e/d (eval-algo-rows bit-mat-mul-rows)
                                  (gsum mat-mul-entry correct-schemep algo-entry scheme-algo
                                        eval-algo-row bit-mat-mul-row)))))

(defthm scheme-algo-eval
  (implies (and (correct-schemep s n) (natp n) (< 0 n) (bit-matp d n n) (bit-matp f n n))
           (equal (eval-algo (scheme-algo s n) d f n)
                  (bit-mat-mul d f n)))
  :hints (("Goal" :in-theory (e/d (eval-algo bit-mat-mul)
                                  (correct-schemep scheme-algo eval-algo-rows bit-mat-mul-rows)))))

(defthm main-3
  (implies (and (correct-schemep sch n) (natp n) (< 0 n))
           (algo-correctp (scheme-algo sch n) n))
  :hints (("Goal" :in-theory (e/d (algo-correctp) (correct-schemep scheme-algo eval-algo bit-mat-mul)))))

