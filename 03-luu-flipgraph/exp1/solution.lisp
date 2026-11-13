;; Strong connectivity of the F2 matrix-multiplication flip graph
;; (flip + plus transformations), for every n >= 2.
;;
;; Representation.  An n x n matrix over F2 is a natural below 2^(n*n),
;; entry (g,h) being bit g*n+h; addition (= subtraction) is LOGXOR.  A
;; rank-one tensor A(x)B(x)C is the triple (A B C) with nonzero factors (over
;; F2 a nonzero rank-one tensor determines its factors).  Schemes are lists of
;; such triples, compared as multisets (PERM: equal multiplicities).  A move
;; (:flip/:plus pos u v) acts on two distinct summands u,v exactly as in the
;; definitions; zero summands are deleted.  MAIN states that between any two
;; schemes S1, S2 for M(n) there is a sequence of valid moves, all of whose
;; intermediate vertices are schemes, ending in S2 (as a multiset).
;;
;; Proof outline.
;;  * Pairs t,t of identical terms can be created and cancelled: any two
;;    summands with different A-factors give a first pair (two plus moves);
;;    with a catalyst c, a pair p,p can be turned into a pair whose factor at
;;    one position is p_pos+c_pos or c_pos (two plus moves and one flip).
;;  * In a scheme S, each elementary matrix E_x is an xor-sum of factors of S
;;    (contract the identity sum S = M(n) at suitable entries), so by steering
;;    a pair one position at a time, S reaches S (+) {t,t} for any rank-one t.
;;  * If the standard scheme S0 = {E_kh(x)E_hl(x)E_kl} is present, every
;;    term can be expanded into elementary terms by plus moves; expansion
;;    preserves tensor entries.  For a scheme X, expand(X) (+) S0 has every
;;    element with even multiplicity, so it cancels completely.
;;  * S -> S (+) S0 (+) S0 -> S0, and S0 -> S0 (+) T (+) T -> T.

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)
(include-book "centaur/bitops/ihs-extensions" :dir :system)
(include-book "centaur/bitops/logbitp-mismatch" :dir :system)

;; ===================================================================
;; Part 1.  Definitions
;; ===================================================================

;; An n x n matrix over F2 is encoded as a natural number below 2^(n*n);
;; entry (g,h) (0-based) is bit number g*n+h.  Matrix addition over F2
;; (= subtraction) is bitwise exclusive or; the zero matrix is 0.

(defun sq (n) (* n n))
(defun matrix-p (n x) (unsigned-byte-p (sq n) x))
(defun mentry (n x g h) (logbitp (+ (* g n) h) x))
(defun madd (x y) (logxor x y))
(defun mzerop (x) (zip x))

;; A term A (x) B (x) C is represented by the list (A B C) of its factors.
;; It is the zero tensor iff one of its factors is zero.  (Over F2 a nonzero
;; rank-one tensor determines its three factors uniquely, so a multiset of
;; nonzero rank-one tensors is faithfully represented by a list of triples,
;; up to permutation.)

(defun term-p (n x)
  (and (true-listp x) (equal (len x) 3)
       (matrix-p n (nth 0 x)) (matrix-p n (nth 1 x)) (matrix-p n (nth 2 x))))
(defun zero-term-p (x)
  (or (mzerop (nth 0 x)) (mzerop (nth 1 x)) (mzerop (nth 2 x))))
(defun rank-one-p (n x) (and (term-p n x) (not (zero-term-p x))))
(defun rank-one-list-p (n l)
  (if (consp l) (and (rank-one-p n (car l)) (rank-one-list-p n (cdr l))) t))

;; Entry (g,h,i,j,k,l) of the tensor A (x) B (x) C is A_gh * B_ij * C_kl.
(defun term-entry (n x g h i j k l)
  (and (mentry n (nth 0 x) g h) (mentry n (nth 1 x) i j) (mentry n (nth 2 x) k l)))
;; Entry of the sum (over F2) of the tensors of a list of terms.
(defun sum-entry (n s g h i j k l)
  (if (consp s)
      (xor (term-entry n (car s) g h i j k l) (sum-entry n (cdr s) g h i j k l))
    nil))
;; The matrix multiplication tensor: (DF)_kl = sum_h D_kh F_hl, so
;; M(n)_{g,h,i,j,k,l} = [g=k][h=i][j=l].
(defun mm-entry (g h i j k l)
  (and (equal g k) (equal h i) (equal j l)))

(defun idx-p (n x) (and (natp x) (< x n)))

(defun-sk sum-is-mm (n s)
  (forall (g h i j k l)
          (implies (and (idx-p n g) (idx-p n h) (idx-p n i)
                        (idx-p n j) (idx-p n k) (idx-p n l))
                   (equal (sum-entry n s g h i j k l) (mm-entry g h i j k l)))))

;; A scheme: a multiset (list) of nonzero rank-one tensors summing to M(n).
(defun scheme-p (n s)
  (and (true-listp s) (rank-one-list-p n s) (sum-is-mm n s)))

;; ----- Multisets: two lists are equal as multisets iff every object
;; occurs equally often in both.
(defun cnt (a x)
  (if (consp x) (+ (if (equal a (car x)) 1 0) (cnt a (cdr x))) 0))
(defun-sk perm (x y) (forall a (equal (cnt a x) (cnt a y))))

;; ----- Flip and plus transformations.
;; Position 0,1,2 = A,B,C.  A move is (kind pos u v), kind :flip or :plus,
;; u and v two (distinct occurrences of) summands of the scheme.
(defun get3 (pos x) (nth pos x))
(defun put3 (pos x val) (update-nth pos val x))

;; Flip on position pos (u and v agree at pos).  For pos = A:
;;   A(x)B(x)C, A(x)B'(x)C'  -->  A(x)B(x)(C+C'), A(x)(B'-B)(x)C'.
;; B and C positions are analogous (cyclically: A->B->C->A).
(defun flip-q (pos) (case pos (0 2) (1 0) (otherwise 1)))
(defun flip-r (pos) (case pos (0 1) (1 2) (otherwise 0)))
(defun flip-results (pos u v)
  (let ((q (flip-q pos)) (r (flip-r pos)))
    (list (put3 q u (madd (get3 q u) (get3 q v)))
          (put3 r v (madd (get3 r v) (get3 r u))))))
;; Plus on position pos.  For pos = A:
;;   v = A'(x)B'(x)C' is replaced by (A'-A)(x)B'(x)C' and A(x)B'(x)C',
;; where A is the A-factor of u.
(defun plus-results (pos u v)
  (list (put3 pos v (madd (get3 pos v) (get3 pos u)))
        (put3 pos v (get3 pos u))))

(defun remove-zero-terms (l)
  (if (consp l)
      (if (zero-term-p (car l))
          (remove-zero-terms (cdr l))
        (cons (car l) (remove-zero-terms (cdr l))))
    nil))

(defun mv-kind (m) (nth 0 m))
(defun mv-pos (m) (nth 1 m))
(defun mv-u (m) (nth 2 m))
(defun mv-v (m) (nth 3 m))

(defun move-valid-p (m s)
  (let ((kind (mv-kind m)) (pos (mv-pos m)) (u (mv-u m)) (v (mv-v m)))
    (and (member kind '(:flip :plus))
         (member pos '(0 1 2))
         (member-equal u s)
         (member-equal v (remove1-equal u s))
         (or (equal kind :plus)
             (equal (get3 pos u) (get3 pos v))))))

;; S' = S \ {u,v} (+) {flip results}   resp.   S' = S \ {v} (+) {plus results},
;; with zero summands deleted.
(defun move-results (m)
  (let ((kind (mv-kind m)) (pos (mv-pos m)) (u (mv-u m)) (v (mv-v m)))
    (remove-zero-terms (if (equal kind :flip)
                           (flip-results pos u v)
                         (plus-results pos u v)))))
(defun move-removed (m s)
  (if (equal (mv-kind m) :flip)
      (remove1-equal (mv-v m) (remove1-equal (mv-u m) s))
    (remove1-equal (mv-v m) s)))
(defun apply-move (m s)
  (append (move-results m) (move-removed m s)))

(defun valid-moves-p (moves s)
  (if (consp moves)
      (and (move-valid-p (car moves) s)
           (valid-moves-p (cdr moves) (apply-move (car moves) s)))
    t))
(defun run-moves (moves s)
  (if (consp moves) (run-moves (cdr moves) (apply-move (car moves) s)) s))

;; There is a directed path from multiset S to multiset S2.
(defun-sk reachable (s s2)
  (exists moves (and (valid-moves-p moves s)
                     (perm (run-moves moves s) s2))))

;; A path in the flip graph for M(n): every step is a flip or plus
;; transformation of the current vertex, and every vertex visited is a scheme.
(defun scheme-path-p (n moves s)
  (if (consp moves)
      (and (move-valid-p (car moves) s)
           (scheme-p n (apply-move (car moves) s))
           (scheme-path-p n (cdr moves) (apply-move (car moves) s)))
    t))
;; There is a directed path in the flip graph from scheme S to the vertex S2
;; (the final list equals S2 as a multiset).
(defun-sk flip-graph-path (n s s2)
  (exists moves (and (scheme-path-p n moves s)
                     (perm (run-moves moves s) s2))))

;; ===================================================================
;; Part 2.  Multisets
;; ===================================================================

(defthm perm-refl (perm x x)
  :hints (("Goal" :in-theory (disable perm-necc))))
(defthm perm-sym (implies (perm x y) (perm y x))
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness y x)))))))
(defthm perm-trans (implies (and (perm x y) (perm y z)) (perm x z))
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness x z)))
                 (:instance perm-necc (a (perm-witness x z)) (x y) (y z))))))
(defequiv perm :hints (("Goal" :in-theory (disable perm))))

(defthm cnt-of-append (equal (cnt a (append x y)) (+ (cnt a x) (cnt a y))))
(defthm cnt-of-remove1
  (equal (cnt a (remove1-equal b x))
         (if (and (equal a b) (member-equal b x)) (1- (cnt a x)) (cnt a x))))
(defthm member-iff-cnt
  (iff (member-equal a x) (< 0 (cnt a x))))
(in-theory (disable member-iff-cnt))

(defmacro perm-by-cnt (x y)
  `(("Goal" :in-theory (disable perm-necc)
     :use ((:instance perm-necc (a (perm-witness ,x ,y)))))))

(defcong perm perm (append x y) 1
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (append x y) (append x-equiv y))) (y x-equiv))))))
(defcong perm perm (append x y) 2
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (append x y) (append x y-equiv))) (x y) (y y-equiv))))))
(defcong perm perm (cons a x) 2
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (cons a x) (cons a x-equiv))) (y x-equiv))))))
(defcong perm iff (member-equal a x) 2
  :hints (("Goal" :in-theory (e/d (member-iff-cnt) (perm-necc))
           :use ((:instance perm-necc (y x-equiv))))))
(defcong perm perm (remove1-equal a x) 2
  :hints (("Goal" :in-theory (e/d (member-iff-cnt) (perm-necc))
           :use ((:instance perm-necc (a (perm-witness (remove1-equal a x) (remove1-equal a x-equiv))) (y x-equiv))
                 (:instance perm-necc (y x-equiv))))))

(defthm perm-append-comm (perm (append x y) (append y x))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (append x y) (append y x)))
                            (x (append x y)) (y (append y x)))))))
(defthm perm-append-assoc-rev (perm (append (append x y) z) (append x (append y z))))
(defthm perm-swap (perm (cons a (cons b x)) (cons b (cons a x)))
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (cons a (cons b x)) (cons b (cons a x))))
                            (x (cons a (cons b x))) (y (cons b (cons a x))))))))
(defthm perm-cons-append (perm (append x (cons a y)) (cons a (append x y)))
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (append x (cons a y)) (cons a (append x y))))
                            (x (append x (cons a y))) (y (cons a (append x y))))))))
(defthm perm-remove1-cons
  (implies (member-equal a x) (perm (cons a (remove1-equal a x)) x))
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (cons a (remove1-equal a x)) x))
                            (x (cons a (remove1-equal a x))) (y x))))))

;; ===================================================================
;; Part 3.  Reachability infrastructure
;; ===================================================================

(in-theory (disable perm))

(defcong perm iff (move-valid-p m s) 2
  :hints (("Goal" :in-theory (e/d (member-iff-cnt) (perm-necc))
           :use ((:instance perm-necc (a (mv-u m)) (x s) (y s-equiv))
                 (:instance perm-necc (a (mv-v m)) (x s) (y s-equiv))))))
(defcong perm perm (move-removed m s) 2
  :hints (("Goal" :in-theory (disable perm-necc)
     :use ((:instance perm-implies-perm-remove1-equal-2 (a (mv-u m)) (x s) (x-equiv s-equiv))
           (:instance perm-implies-perm-remove1-equal-2 (a (mv-v m)) (x s) (x-equiv s-equiv))
           (:instance perm-implies-perm-remove1-equal-2 (a (mv-v m))
                      (x (remove1-equal (mv-u m) s)) (x-equiv (remove1-equal (mv-u m) s-equiv)))))))
(in-theory (disable move-results move-removed move-valid-p))
(defcong perm perm (apply-move m s) 2)
(in-theory (disable apply-move))
(defun ind2 (moves s s2)
  (if (consp moves)
      (ind2 (cdr moves) (apply-move (car moves) s) (apply-move (car moves) s2))
    (list s s2)))
(defthm valid-moves-perm-lemma
  (implies (perm s s2)
           (and (equal (valid-moves-p moves s) (valid-moves-p moves s2))
                (perm (run-moves moves s) (run-moves moves s2))))
  :rule-classes nil
  :hints (("Goal" :induct (ind2 moves s s2))
          ("Subgoal *1/2" :use ((:instance perm-implies-perm-apply-move-2 (m (car moves)) (s s) (s-equiv s2))
                 (:instance perm-implies-iff-move-valid-p-2 (m (car moves)) (s s) (s-equiv s2))))))
(defcong perm iff (valid-moves-p moves s) 2
  :hints (("Goal" :use ((:instance valid-moves-perm-lemma (s2 s-equiv))))))
(defcong perm perm (run-moves moves s) 2
  :hints (("Goal" :use ((:instance valid-moves-perm-lemma (s2 s-equiv))))))

(defcong perm iff (reachable x y) 1
  :hints (("Goal" :cases ((reachable x y)))
          ("Subgoal 2" :use ((:instance reachable-suff (s x) (s2 y) (moves (reachable-witness x-equiv y)))
                             (:instance valid-moves-perm-lemma (s x) (s2 x-equiv) (moves (reachable-witness x-equiv y)))))
          ("Subgoal 1" :use ((:instance reachable-suff (s x-equiv) (s2 y) (moves (reachable-witness x y)))
                             (:instance valid-moves-perm-lemma (s x) (s2 x-equiv) (moves (reachable-witness x y)))))))
(defcong perm iff (reachable x y) 2
  :hints (("Goal" :cases ((reachable x y)))
          ("Subgoal 2" :use ((:instance reachable-suff (s x) (s2 y) (moves (reachable-witness x y-equiv)))))
          ("Subgoal 1" :use ((:instance reachable-suff (s x) (s2 y-equiv) (moves (reachable-witness x y)))))))

(defthm valid-moves-append
  (equal (valid-moves-p (append m1 m2) s)
         (and (valid-moves-p m1 s) (valid-moves-p m2 (run-moves m1 s)))))
(defthm run-moves-append
  (equal (run-moves (append m1 m2) s) (run-moves m2 (run-moves m1 s))))

(in-theory (disable reachable))

(defthm reachable-refl (implies (perm x y) (reachable x y))
  :hints (("Goal" :use ((:instance reachable-suff (s x) (s2 y) (moves nil))))))

(defthm reachable-trans
  (implies (and (reachable y z) (reachable x y))
           (reachable x z))
  :hints (("Goal" :in-theory (e/d (reachable) (reachable-suff))
           :use ((:instance reachable-suff (s x) (s2 z)
                            (moves (append (reachable-witness x y) (reachable-witness y z))))))))

(defthm reachable-step
  (implies (move-valid-p m s) (reachable s (apply-move m s)))
  :hints (("Goal" :in-theory (disable move-valid-p apply-move reachable-suff)
           :use ((:instance reachable-suff (s2 (apply-move m s)) (moves (list m)))))))

;; ===================================================================
;; Part 4.  Basic derived moves
;; ===================================================================
(defun good3 (x)
  (and (true-listp x) (equal (len x) 3)
       (posp (nth 0 x)) (posp (nth 1 x)) (posp (nth 2 x))))
(defun pos-p (pos) (member pos '(0 1 2)))

(defthm logxor-zero-iff
  (implies (and (natp a) (natp b))
           (equal (equal (logxor a b) 0) (equal a b))))
(defthm natp-logxor (implies (and (natp a) (natp b)) (natp (logxor a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm posp-logxor
  (implies (and (natp a) (natp b) (not (equal a b))) (posp (logxor a b)))
  :hints (("Goal" :use logxor-zero-iff :in-theory (disable logxor-zero-iff))))
(defthm good3-not-zero (implies (good3 x) (not (zero-term-p x))))
(defthm good3-put3
  (implies (and (good3 x) (pos-p pos) (posp val))
           (good3 (put3 pos x val)))
  :hints (("Goal" :in-theory (enable nth update-nth))))
(defthm get3-put3
  (equal (get3 pos (put3 pos x val)) val))
(defthm get3-put3-diff
  (implies (and (not (equal pos1 pos2)) (natp pos1) (natp pos2))
           (equal (get3 pos1 (put3 pos2 x val)) (get3 pos1 x))))
(defthm put3-put3
  (equal (put3 pos (put3 pos x v1) v2) (put3 pos x v2)))
(defthm len3-form
  (implies (and (true-listp x) (equal (len x) 3))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x)) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nth len))))
(defthm put3-get3
  (implies (and (good3 x) (pos-p pos)) (equal (put3 pos x (get3 pos x)) x))
  :hints (("Goal" :in-theory (enable nth update-nth) :use len3-form)))
(defthm natp-get3 (implies (and (good3 x) (pos-p pos)) (posp (get3 pos x)))
  :rule-classes (:rewrite :type-prescription))
(in-theory (disable get3 put3 good3 pos-p))

(defun plus-a (pos v c) (put3 pos v (logxor (get3 pos v) (get3 pos c))))
(defun plus-b (pos v c) (put3 pos v (get3 pos c)))

;; plus with catalyst c on the front term v
(defthm plus-front-valid
  (implies (and (pos-p pos) (member-equal c rest)
                (not (equal (get3 pos c) (get3 pos v))))
           (move-valid-p (list :plus pos c v) (cons v rest)))
  :hints (("Goal" :in-theory (enable move-valid-p pos-p))))
(defthm plus-front-apply
  (implies (and (pos-p pos) (good3 v)
                (posp (get3 pos c))
                (not (equal (get3 pos c) (get3 pos v))))
           (equal (apply-move (list :plus pos c v) (cons v rest))
                  (list* (plus-a pos v c) (plus-b pos v c) rest)))
  :hints (("Goal" :in-theory (enable apply-move move-results move-removed))))
(defthm plus-front
  (implies (and (pos-p pos) (good3 v) (member-equal c rest)
                (posp (get3 pos c))
                (not (equal (get3 pos c) (get3 pos v))))
           (reachable (cons v rest) (list* (plus-a pos v c) (plus-b pos v c) rest)))
  :hints (("Goal" :in-theory (disable reachable-step plus-a plus-b)
           :use ((:instance reachable-step (m (list :plus pos c v)) (s (cons v rest)))))))

;; cancelling two equal terms (flip on two identical summands)
(defthm cancel-front
  (reachable (list* z z rest) rest)
  :hints (("Goal" :in-theory (e/d (move-valid-p apply-move move-results move-removed get3 put3)
                                  (reachable-step))
           :use ((:instance reachable-step (m (list :flip 0 z z)) (s (list* z z rest)))))))

(in-theory (disable plus-a plus-b))

(defthm pl-facts
  (implies (and (pos-p pos) (good3 v) (posp (get3 pos c)))
           (and (equal (get3 pos (plus-b pos v c)) (get3 pos c))
                (equal (plus-a pos v (plus-b pos v c)) (plus-a pos v c))
                (equal (plus-b pos v (plus-b pos v c)) (plus-b pos v c))))
  :hints (("Goal" :in-theory (enable plus-a plus-b))))
(defthm pl-good
  (implies (and (pos-p pos) (good3 v) (posp (get3 pos c))
                (not (equal (get3 pos c) (get3 pos v))))
           (and (good3 (plus-a pos v c)) (good3 (plus-b pos v c))))
  :hints (("Goal" :in-theory (enable plus-a plus-b))))

;; From a pair p,p and a catalyst c: reach pair plus-a,plus-a or pair plus-b,plus-b.
(defthm pair-shift-lemma
  (implies (and (pos-p pos) (good3 p) (member-equal c rest)
                (posp (get3 pos c))
                (not (equal (get3 pos c) (get3 pos p))))
           (reachable (list* p p rest)
                      (list* (plus-a pos p c) (plus-b pos p c) (plus-a pos p c) (plus-b pos p c) rest)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable reachable-trans plus-front)
           :use ((:instance plus-front (v p) (rest (cons p rest)))
                 (:instance plus-front (v p) (c (plus-b pos p c))
                            (rest (list* (plus-a pos p c) (plus-b pos p c) rest)))
                 (:instance reachable-trans (x (list* p p rest))
                            (y (list* p (plus-a pos p c) (plus-b pos p c) rest))
                            (z (list* (plus-a pos p c) (plus-b pos p c) (plus-a pos p c) (plus-b pos p c) rest)))))))

(defthm pair-shift-1
  (implies (and (pos-p pos) (good3 p) (member-equal c rest)
                (posp (get3 pos c))
                (not (equal (get3 pos c) (get3 pos p))))
           (reachable (list* p p rest) (list* (plus-a pos p c) (plus-a pos p c) rest)))
  :hints (("Goal" :in-theory (disable reachable-trans cancel-front)
           :use (pair-shift-lemma
                 (:instance cancel-front (z (plus-b pos p c)) (rest (list* (plus-a pos p c) (plus-a pos p c) rest)))
                 (:instance reachable-trans (x (list* p p rest))
                            (y (list* (plus-a pos p c) (plus-b pos p c) (plus-a pos p c) (plus-b pos p c) rest))
                            (z (list* (plus-a pos p c) (plus-a pos p c) rest)))))))
(defthm pair-shift-2
  (implies (and (pos-p pos) (good3 p) (member-equal c rest)
                (posp (get3 pos c))
                (not (equal (get3 pos c) (get3 pos p))))
           (reachable (list* p p rest) (list* (plus-b pos p c) (plus-b pos p c) rest)))
  :hints (("Goal" :in-theory (disable reachable-trans cancel-front)
           :use (pair-shift-lemma
                 (:instance cancel-front (z (plus-a pos p c)) (rest (list* (plus-b pos p c) (plus-b pos p c) rest)))
                 (:instance reachable-trans (x (list* p p rest))
                            (y (list* (plus-a pos p c) (plus-b pos p c) (plus-a pos p c) (plus-b pos p c) rest))
                            (z (list* (plus-b pos p c) (plus-b pos p c) rest)))))))

;; ===================================================================
;; Part 5.  Steering a pair p,p to an arbitrary factor at one position
;; ===================================================================
(defun xsum (l) (if (consp l) (logxor (car l) (xsum (cdr l))) 0))
(defun factors-at (pos l) (if (consp l) (cons (get3 pos (car l)) (factors-at pos (cdr l))) nil))
(defun find-cat (pos x l)
  (if (consp l) (if (equal (get3 pos (car l)) x) (car l) (find-cat pos x (cdr l))) nil))
(defthm find-cat-ok
  (implies (member-equal x (factors-at pos l))
           (and (member-equal (find-cat pos x l) l)
                (equal (get3 pos (find-cat pos x l)) x))))
(defun avail (pos xs rest)
  (if (consp xs)
      (and (posp (car xs)) (member-equal (car xs) (factors-at pos rest))
           (avail pos (cdr xs) rest))
    t))
(defthm natp-xsum (implies (avail pos l rest) (natp (xsum l)))
  :rule-classes (:rewrite :type-prescription))

(defthm pair-shift-put-1
  (implies (and (pos-p pos) (good3 p) (posp s) (posp x)
                (member-equal x (factors-at pos rest))
                (not (equal x s)))
           (reachable (list* (put3 pos p s) (put3 pos p s) rest)
                      (list* (put3 pos p (logxor s x)) (put3 pos p (logxor s x)) rest)))
  :hints (("Goal" :in-theory (e/d (plus-a plus-b) (pair-shift-1))
           :use ((:instance pair-shift-1 (p (put3 pos p s)) (c (find-cat pos x rest)))))))
(defthm pair-shift-put-2
  (implies (and (pos-p pos) (good3 p) (posp s) (posp x)
                (member-equal x (factors-at pos rest))
                (not (equal x s)))
           (reachable (list* (put3 pos p s) (put3 pos p s) rest)
                      (list* (put3 pos p x) (put3 pos p x) rest)))
  :hints (("Goal" :in-theory (e/d (plus-a plus-b) (pair-shift-2))
           :use ((:instance pair-shift-2 (p (put3 pos p s)) (c (find-cat pos x rest)))))))

(defthm logxor-cancel-left
  (equal (logxor x (logxor x y)) (ifix y)))

(defun build-ind (s l)
  (cond ((endp l) s)
        ((not (equal (car l) s)) (build-ind (logxor s (car l)) (cdr l)))
        ((endp (cdr l)) s)
        ((not (equal (cadr l) s)) (build-ind (cadr l) (cddr l)))
        (t (build-ind s (cddr l)))))

(defthm build-iter
  (implies (and (pos-p pos) (good3 p) (posp s) (avail pos l rest)
                (not (equal (logxor s (xsum l)) 0)))
           (reachable (list* (put3 pos p s) (put3 pos p s) rest)
                      (list* (put3 pos p (logxor s (xsum l)))
                             (put3 pos p (logxor s (xsum l))) rest)))
  :hints (("Goal" :induct (build-ind s l))))

(defthm build-pair
  (implies (and (pos-p pos) (good3 p) (avail pos l rest)
                (not (equal (xsum l) 0)))
           (reachable (list* p p rest)
                      (list* (put3 pos p (xsum l)) (put3 pos p (xsum l)) rest)))
  :hints (("Goal" :in-theory (disable build-iter pair-shift-put-2 reachable-trans)
           :cases ((equal (car l) (get3 pos p)))
           :expand ((xsum l) (avail pos l rest)))
          ("Subgoal 2" :use ((:instance build-iter (s (car l)) (l (cdr l)))
                             (:instance pair-shift-put-2 (s (get3 pos p)) (x (car l)))
                             (:instance reachable-trans
                                        (x (list* p p rest))
                                        (y (list* (put3 pos p (car l)) (put3 pos p (car l)) rest))
                                        (z (list* (put3 pos p (xsum l)) (put3 pos p (xsum l)) rest)))))
          ("Subgoal 1" :use ((:instance build-iter (s (car l)) (l (cdr l)))))))

;; ===================================================================
;; Part 6.  Tensor entries in flat coordinates
;; ===================================================================
(defun tentry (s a b c)
  (if (consp s)
      (xor (and (logbitp a (nth 0 (car s))) (logbitp b (nth 1 (car s)))
                (logbitp c (nth 2 (car s))))
           (tentry (cdr s) a b c))
    nil))
(defthm sum-entry-is-tentry
  (equal (sum-entry n s g h i j k l)
         (tentry s (+ (* g n) h) (+ (* i n) j) (+ (* k n) l))))

(defun mflat (n a b c)
  (mm-entry (floor a n) (mod a n) (floor b n) (mod b n) (floor c n) (mod c n)))

(defthm flat-decomp
  (implies (and (natp a) (posp n))
           (equal (+ (* (floor a n) n) (mod a n)) a)))
(defthm floor-bound-lemma
  (implies (and (natp a) (posp n) (< a (* n n)))
           (< (* a (expt n -2)) 1))
  :hints (("Goal" :nonlinearp t)))
(defthm floor-bound
  (implies (and (natp a) (posp n) (< a (* n n)))
           (< (floor a n) n))
  :rule-classes (:rewrite :linear))
(in-theory (disable sum-is-mm))

(defthm scheme-tentry
  (implies (and (sum-is-mm n s) (posp n)
                (natp a) (< a (* n n)) (natp b) (< b (* n n)) (natp c) (< c (* n n)))
           (equal (tentry s a b c) (mflat n a b c)))
  :hints (("Goal" :in-theory (disable sum-is-mm-necc sum-entry-is-tentry flat-decomp)
           :use ((:instance sum-is-mm-necc (g (floor a n)) (h (mod a n))
                            (i (floor b n)) (j (mod b n)) (k (floor c n)) (l (mod c n)))
                 (:instance sum-entry-is-tentry (g (floor a n)) (h (mod a n))
                            (i (floor b n)) (j (mod b n)) (k (floor c n)) (l (mod c n)))
                 (:instance flat-decomp (a a))
                 (:instance flat-decomp (a b))
                 (:instance flat-decomp (a c))))))

(defun o1 (pos) (case pos (0 1) (1 0) (otherwise 0)))
(defun o2 (pos) (case pos (0 2) (1 2) (otherwise 1)))
(defun sel (pos s i j)
  (if (consp s)
      (if (and (logbitp i (get3 (o1 pos) (car s))) (logbitp j (get3 (o2 pos) (car s))))
          (cons (get3 pos (car s)) (sel pos (cdr s) i j))
        (sel pos (cdr s) i j))
    nil))
(defun tent3 (pos s k i j)
  (case pos (0 (tentry s k i j)) (1 (tentry s i k j)) (otherwise (tentry s i j k))))

(defthm logbitp-non-integer
  (implies (not (integerp x)) (not (logbitp k x)))
  :hints (("Goal" :in-theory (enable logbitp))))
(defthm logbitp-xsum-sel
  (implies (pos-p pos)
           (equal (logbitp k (xsum (sel pos s i j))) (tent3 pos s k i j)))
  :hints (("Goal" :in-theory (enable get3 pos-p))))

(defthm flat-eq
  (implies (and (natp a) (natp b) (posp n))
           (equal (and (equal (floor a n) (floor b n)) (equal (mod a n) (mod b n)))
                  (equal a b)))
  :hints (("Goal" :in-theory (disable flat-decomp)
           :use (flat-decomp (:instance flat-decomp (a b))))))

(defun esel (pos s n x)
  (case pos
    (0 (sel 0 s (* n (mod x n)) (* n (floor x n))))
    (1 (sel 1 s (floor x n) (mod x n)))
    (otherwise (sel 2 s (* n (floor x n)) (mod x n)))))

(defthm mod-bound2 (implies (and (natp x) (posp n)) (< (* n (mod x n)) (* n n)))
  :hints (("Goal" :nonlinearp t)))
(defthm floor-bound2 (implies (and (natp x) (posp n) (< x (* n n))) (< (* n (floor x n)) (* n n)))
  :hints (("Goal" :nonlinearp t)))

(defthm small-bound (implies (and (natp x) (posp n) (< x n)) (< x (* n n)))
  :hints (("Goal" :nonlinearp t)))
(defthm mod-bound1 (implies (and (natp x) (posp n)) (< (mod x n) (* n n)))
  :hints (("Goal" :nonlinearp t)))
(defthm floor-bound1 (implies (and (natp x) (posp n) (< x (* n n))) (< (floor x n) (* n n)))
  :hints (("Goal" :nonlinearp t)))

(defthm cube-bound (implies (and (posp n) (natp k) (< k (expt n 2))) (< k (expt n 3)))
  :hints (("Goal" :nonlinearp t)))
(defthm mflat-0
  (implies (and (natp x) (natp k) (posp n) (< x (* n n)))
           (equal (mflat n k (* n (mod x n)) (* n (floor x n))) (equal k x)))
  :hints (("Goal" :in-theory (disable flat-eq) :use ((:instance flat-eq (a k) (b x))))))
(defthm mflat-1
  (implies (and (natp x) (natp k) (posp n) (< x (* n n)))
           (equal (mflat n (floor x n) k (mod x n)) (equal k x)))
  :hints (("Goal" :in-theory (disable flat-eq) :use ((:instance flat-eq (a k) (b x))))))
(defthm mflat-2
  (implies (and (natp x) (natp k) (posp n) (< x (* n n)))
           (equal (mflat n (* n (floor x n)) (mod x n) k) (equal k x)))
  :hints (("Goal" :in-theory (disable flat-eq) :use ((:instance flat-eq (a k) (b x))))))
(in-theory (disable mflat))

(defthm logbitp-xsum-esel
  (implies (and (pos-p pos) (sum-is-mm n s) (posp n)
                (natp x) (< x (* n n)) (natp k) (< k (* n n)))
           (equal (logbitp k (xsum (esel pos s n x)))
                  (equal k x)))
  :hints (("Goal" :in-theory (e/d (pos-p) (scheme-tentry floor mod))
           :use ((:instance scheme-tentry (a k) (b (* n (mod x n))) (c (* n (floor x n))))
                 (:instance scheme-tentry (b k) (a (floor x n)) (c (mod x n)))
                 (:instance scheme-tentry (c k) (a (* n (floor x n))) (b (mod x n)))))))

(defthm equal-by-bits
  (implies (and (natp x) (natp y)
                (equal (logbitp (logbitp-mismatch x y) x)
                       (logbitp (logbitp-mismatch x y) y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use ((:instance bitops::logbitp-mismatch-correct (a x) (b y))
                        (:instance bitops::logbitp-mismatch-under-iff (a x) (b y))))))
(defthm big-bit
  (implies (and (natp k) (natp i) (<= k i) (unsigned-byte-p k x)) (not (logbitp i x)))
  :hints (("Goal" :use ((:instance bitops::expt-2-lower-bound-by-logbitp (n i)))
           :in-theory (enable unsigned-byte-p))))
(defthm natp-mismatch
  (implies (bitops::logbitp-mismatch x y) (natp (bitops::logbitp-mismatch x y)))
  :hints (("Goal" :use ((:instance bitops::integerp-of-logbitp-mismatch (a x) (b y))))))

(defthm natp-sq (implies (natp n) (natp (sq n))) :rule-classes (:rewrite :type-prescription))
(defthm sq-linear (implies (natp n) (equal (sq n) (* n n))) :rule-classes :linear)
(in-theory (disable sq))
(defun ubp-list (k l)
  (if (consp l) (and (unsigned-byte-p k (car l)) (ubp-list k (cdr l))) t))
(defthm ubp-xsum (implies (and (natp k) (ubp-list k l)) (unsigned-byte-p k (xsum l))))
(defthm rank-one-facts
  (implies (and (rank-one-p n x) (pos-p pos) (natp n))
           (and (unsigned-byte-p (sq n) (get3 pos x))
                (posp (get3 pos x))
                (good3 x)))
  :hints (("Goal" :in-theory (enable pos-p get3 good3))))
(defthm ubp-list-sel
  (implies (and (rank-one-list-p n s) (natp n) (pos-p pos2))
           (ubp-list (sq n) (sel pos2 s i j)))
  :hints (("Goal" :in-theory (disable rank-one-p))))
(defthm ubp-list-esel
  (implies (and (rank-one-list-p n s) (natp n) (pos-p pos))
           (ubp-list (sq n) (esel pos s n x)))
  :hints (("Goal" :in-theory (e/d (pos-p) (rank-one-p)))))

(defthm xsum-esel
  (implies (and (pos-p pos) (sum-is-mm n s) (rank-one-list-p n s) (posp n)
                (natp x) (< x (* n n)))
           (equal (xsum (esel pos s n x)) (expt 2 x)))
  :hints (("Goal" :in-theory (e/d () (esel logbitp-xsum-esel big-bit ubp-xsum))
           :use ((:instance equal-by-bits (x (xsum (esel pos s n x))) (y (expt 2 x)))
                 (:instance logbitp-xsum-esel (k (bitops::logbitp-mismatch (xsum (esel pos s n x)) (expt 2 x))))
                 (:instance big-bit (k (sq n)) (x (xsum (esel pos s n x)))
                            (i (bitops::logbitp-mismatch (xsum (esel pos s n x)) (expt 2 x))))
                 (:instance ubp-xsum (k (sq n)) (l (esel pos s n x)))))))

;; ===================================================================
;; Part 7.  Every matrix is an xor-sum of available factors
;; ===================================================================
(defun bits-below (k p)
  (if (zp k) nil
    (if (logbitp (1- k) p) (cons (1- k) (bits-below (1- k) p)) (bits-below (1- k) p))))
(defun sume (xs) (if (consp xs) (logxor (expt 2 (car xs)) (sume (cdr xs))) 0))

(defthm logbitp-sume-bits-below
  (implies (natp j)
           (equal (logbitp j (sume (bits-below k p)))
                  (and (< j (nfix k)) (logbitp j p)))))
(defthm natp-sume (natp (sume xs)) :rule-classes (:rewrite :type-prescription))

(defthm sume-bits-below
  (implies (and (natp k) (unsigned-byte-p k p))
           (equal (sume (bits-below k p)) p))
  :hints (("Goal" :in-theory (disable logbitp-sume-bits-below big-bit bitops::logbitp-mismatch-correct)
           :use ((:instance equal-by-bits (x (sume (bits-below k p))) (y p))
                 (:instance logbitp-sume-bits-below
                            (j (bitops::logbitp-mismatch (sume (bits-below k p)) p)))
                 (:instance big-bit (x p) (i (bitops::logbitp-mismatch (sume (bits-below k p)) p)))))))

(defun all-below (k xs) (if (consp xs) (and (natp (car xs)) (< (car xs) k) (all-below k (cdr xs))) t))
(defthm all-below-mono
  (implies (and (all-below k xs) (<= k k2)) (all-below k2 xs)))
(defthm all-below-bits-below (implies (natp k) (all-below k (bits-below k p))))

(defun tlist (pos s n xs)
  (if (consp xs) (append (esel pos s n (car xs)) (tlist pos s n (cdr xs))) nil))
(defthm xsum-append (equal (xsum (append a b)) (logxor (xsum a) (xsum b))))
(defthm xsum-tlist
  (implies (and (pos-p pos) (sum-is-mm n s) (rank-one-list-p n s) (posp n)
                (all-below (sq n) xs))
           (equal (xsum (tlist pos s n xs)) (sume xs)))
  :hints (("Goal" :in-theory (disable esel))))

(defthm avail-append (equal (avail pos (append a b) rest) (and (avail pos a rest) (avail pos b rest))))
(defthm member-factors-at
  (implies (member-equal x rest) (member-equal (get3 pos x) (factors-at pos rest))))
(defthm avail-sel
  (implies (and (rank-one-list-p n s) (natp n) (pos-p pos) (subsetp-equal s rest))
           (avail pos (sel pos s i j) rest))
  :hints (("Goal" :in-theory (disable rank-one-p))))
(defthm avail-tlist
  (implies (and (rank-one-list-p n s) (natp n) (pos-p pos) (subsetp-equal s rest))
           (avail pos (tlist pos s n xs) rest))
  :hints (("Goal" :in-theory (e/d (pos-p) (rank-one-p)))))

(defun target-list (pos s n p) (tlist pos s n (bits-below (sq n) p)))
(defthm target-list-ok
  (implies (and (pos-p pos) (scheme-p n s) (posp n) (unsigned-byte-p (sq n) p)
                (subsetp-equal s rest))
           (and (equal (xsum (target-list pos s n p)) p)
                (avail pos (target-list pos s n p) rest))))
(in-theory (disable target-list))

;; ===================================================================
;; Part 8.  Two summands with different A-factors exist (n >= 2)
;; ===================================================================
(defun has-diff (pos v s)
  (if (consp s) (or (not (equal (get3 pos (car s)) v)) (has-diff pos v (cdr s))) nil))
(defun find-diff (pos v s)
  (if (consp s) (if (equal (get3 pos (car s)) v) (find-diff pos v (cdr s)) (car s)) nil))
(defthm find-diff-ok-1
  (implies (has-diff pos v s)
           (not (equal (get3 pos (find-diff pos v s)) v)))
  :hints (("Goal" :induct (find-diff pos v s))))
(defthm find-diff-ok-2
  (implies (has-diff pos v s)
           (member-equal (find-diff pos v s) s))
  :hints (("Goal" :induct (find-diff pos v s))))
(defthm no-diff-xsum-sel
  (implies (not (has-diff pos v s))
           (or (equal (xsum (sel pos s i j)) 0)
               (equal (xsum (sel pos s i j)) (ifix v))))
  :rule-classes nil)

(defthm scheme-has-diff
  (implies (and (scheme-p n s) (natp n) (<= 2 n))
           (has-diff 0 v s))
  :hints (("Goal" :in-theory (disable xsum-esel) :do-not-induct t
           :use ((:instance no-diff-xsum-sel (pos 0) (i 0) (j 0))
                 (:instance no-diff-xsum-sel (pos 0) (i (* n (mod 1 n))) (j (* n (floor 1 n))))
                 (:instance xsum-esel (pos 0) (x 0))
                 (:instance xsum-esel (pos 0) (x 1))))))

;; ===================================================================
;; Part 9.  Creating a pair t,t of an arbitrary rank-one tensor
;; ===================================================================
(defthm reachable-trans-2
  (implies (and (reachable x y) (reachable y z))
           (reachable x z)))

(defthm reach-perm2
  (implies (and (reachable a b) (perm b c)) (reachable a c)) :rule-classes nil)
(defthm reach-perm1
  (implies (and (reachable a b) (perm a c)) (reachable c b)) :rule-classes nil)
(defthm logxor-same-right
  (implies (and (natp x) (natp y)) (equal (equal y (logxor x y)) (equal x 0))))
(defthm logxor-same-right2
  (implies (and (natp x) (natp y)) (equal (equal y (logxor y x)) (equal x 0))))

(defthm base-pair-step1
  (implies (and (good3 x) (good3 y) (member-equal y r)
                (not (equal (get3 0 y) (get3 0 x))))
           (reachable (cons x r)
                      (list* (put3 0 x (logxor (get3 0 x) (get3 0 y)))
                             (put3 0 x (get3 0 y)) r)))
  :hints (("Goal" :in-theory (e/d (plus-a plus-b pos-p) (plus-front))
           :use ((:instance plus-front (pos 0) (v x) (c y) (rest r))))))
(defthm base-pair-step2
  (implies (and (good3 x) (good3 y)
                (not (equal (get3 0 y) (get3 0 x))))
           (reachable (list* (put3 0 x (logxor (get3 0 x) (get3 0 y)))
                             (put3 0 x (get3 0 y)) r)
                      (list* x (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) r)))
  :hints (("Goal" :in-theory (e/d (plus-a plus-b pos-p) (plus-front))
           :use ((:instance plus-front (pos 0) (v (put3 0 x (logxor (get3 0 x) (get3 0 y))))
                            (c (put3 0 x (get3 0 y)))
                            (rest (cons (put3 0 x (get3 0 y)) r)))))))
(defthm perm-rot3 (perm (list* x b b r) (list* b b (cons x r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (list* x b b r) (list* b b (cons x r))))
                            (x (list* x b b r)) (y (list* b b (cons x r))))))))

(defthm base-pair
  (implies (and (good3 x) (good3 y) (member-equal x rest) (member-equal y rest)
                (not (equal (get3 0 y) (get3 0 x))))
           (reachable rest (list* (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) rest)))
  :hints (("Goal" :in-theory (disable reachable-trans reachable-trans-2 base-pair-step1 base-pair-step2
                                      perm-remove1-cons)
           :use ((:instance base-pair-step1 (r (remove1-equal x rest)))
                 (:instance base-pair-step2 (r (remove1-equal x rest)))
                 (:instance perm-remove1-cons (a x) (x rest))
                 (:instance reachable-trans
                            (x (cons x (remove1-equal x rest)))
                            (y (list* (put3 0 x (logxor (get3 0 x) (get3 0 y)))
                                      (put3 0 x (get3 0 y)) (remove1-equal x rest)))
                            (z (list* x (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) (remove1-equal x rest))))
                 (:instance perm-rot3 (b (put3 0 x (get3 0 y))) (r (remove1-equal x rest)))
                 (:instance reach-perm2
                            (a (cons x (remove1-equal x rest)))
                            (b (list* x (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) (remove1-equal x rest)))
                            (c (list* (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) (cons x (remove1-equal x rest)))))
                 (:instance reach-perm1
                            (a (cons x (remove1-equal x rest)))
                            (b (list* (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) (cons x (remove1-equal x rest))))
                            (c rest))
                 (:instance perm-implies-perm-cons-2
                            (a (put3 0 x (get3 0 y)))
                            (x (cons (put3 0 x (get3 0 y)) (cons x (remove1-equal x rest))))
                            (x-equiv (cons (put3 0 x (get3 0 y)) rest)))
                 (:instance perm-implies-perm-cons-2
                            (a (put3 0 x (get3 0 y)))
                            (x (cons x (remove1-equal x rest)))
                            (x-equiv rest))
                 (:instance reach-perm2
                            (a rest)
                            (b (list* (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) (cons x (remove1-equal x rest))))
                            (c (list* (put3 0 x (get3 0 y)) (put3 0 x (get3 0 y)) rest)))))))

(defthm steer
  (implies (and (pos-p pos) (scheme-p n ctx) (posp n) (subsetp-equal ctx rest)
                (good3 p) (unsigned-byte-p (sq n) v) (posp v))
           (reachable (list* p p rest) (list* (put3 pos p v) (put3 pos p v) rest)))
  :hints (("Goal" :in-theory (disable build-pair target-list-ok scheme-p)
           :use ((:instance build-pair (l (target-list pos ctx n v)))
                 (:instance target-list-ok (s ctx) (p v))))))

(defthm put3-all
  (implies (and (good3 x) (true-listp tt) (equal (len tt) 3))
           (equal (put3 2 (put3 1 (put3 0 x (nth 0 tt)) (nth 1 tt)) (nth 2 tt)) tt))
  :hints (("Goal" :in-theory (enable put3 good3 update-nth nth)
           :use ((:instance len3-form (x tt))))))

(defthm rank-one-good3
  (implies (and (rank-one-p n x) (natp n)) (good3 x))
  :hints (("Goal" :in-theory (enable good3))))
(defthm scheme-good3-members
  (implies (and (rank-one-list-p n s) (natp n) (member-equal x s))
           (good3 x))
  :hints (("Goal" :in-theory (disable rank-one-p))))

(defthm rank-one-tt
  (implies (and (rank-one-p n tt) (natp n))
           (and (true-listp tt) (equal (len tt) 3)
                (unsigned-byte-p (sq n) (nth 0 tt)) (posp (nth 0 tt))
                (unsigned-byte-p (sq n) (nth 1 tt)) (posp (nth 1 tt))
                (unsigned-byte-p (sq n) (nth 2 tt)) (posp (nth 2 tt))))
  :hints (("Goal" :in-theory (enable rank-one-p))))

(defthm scheme-p-forward
  (implies (scheme-p n s)
           (and (true-listp s) (rank-one-list-p n s) (sum-is-mm n s)))
  :rule-classes :forward-chaining)

(defthm steer-all
  (implies (and (scheme-p n ctx) (posp n) (subsetp-equal ctx rest)
                (good3 p) (rank-one-p n tt))
           (reachable (list* p p rest) (list* tt tt rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (reachable-trans reachable-trans-2 steer scheme-p put3-all
                               rank-one-p rank-one-tt))
           :use ((:instance rank-one-tt)
                 (:instance good3-put3 (pos 0) (x p) (val (nth 0 tt)))
                 (:instance good3-put3 (pos 1) (x (put3 0 p (nth 0 tt))) (val (nth 1 tt)))
                 (:instance steer (pos 0) (v (nth 0 tt)))
                 (:instance steer (pos 1) (p (put3 0 p (nth 0 tt))) (v (nth 1 tt)))
                 (:instance steer (pos 2) (p (put3 1 (put3 0 p (nth 0 tt)) (nth 1 tt))) (v (nth 2 tt)))
                 (:instance put3-all (x p))
                 (:instance reachable-trans
                            (x (list* p p rest))
                            (y (list* (put3 0 p (nth 0 tt)) (put3 0 p (nth 0 tt)) rest))
                            (z (list* (put3 1 (put3 0 p (nth 0 tt)) (nth 1 tt))
                                      (put3 1 (put3 0 p (nth 0 tt)) (nth 1 tt)) rest)))
                 (:instance reachable-trans
                            (x (list* p p rest))
                            (y (list* (put3 1 (put3 0 p (nth 0 tt)) (nth 1 tt))
                                      (put3 1 (put3 0 p (nth 0 tt)) (nth 1 tt)) rest))
                            (z (list* tt tt rest)))))))

(defthm member-subsetp
  (implies (and (member-equal x a) (subsetp-equal a b)) (member-equal x b))
  :rule-classes nil)
(defthm some-pair
  (implies (and (scheme-p n ctx) (natp n) (<= 2 n) (subsetp-equal ctx rest))
           (and (good3 (put3 0 (car ctx) (get3 0 (find-diff 0 (get3 0 (car ctx)) ctx))))
                (reachable rest (list* (put3 0 (car ctx) (get3 0 (find-diff 0 (get3 0 (car ctx)) ctx)))
                                       (put3 0 (car ctx) (get3 0 (find-diff 0 (get3 0 (car ctx)) ctx)))
                                       rest))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (pos-p) (base-pair scheme-p scheme-has-diff find-diff-ok-1 find-diff-ok-2))
           :use ((:instance scheme-has-diff (s ctx) (v (get3 0 (car ctx))))
                 (:instance find-diff-ok-1 (pos 0) (v (get3 0 (car ctx))) (s ctx))
                 (:instance find-diff-ok-2 (pos 0) (v (get3 0 (car ctx))) (s ctx))
                 (:instance scheme-good3-members (s ctx) (x (car ctx)))
                 (:instance scheme-good3-members (s ctx) (x (find-diff 0 (get3 0 (car ctx)) ctx)))
                 (:instance member-subsetp (x (car ctx)) (a ctx) (b rest))
                 (:instance member-subsetp (x (find-diff 0 (get3 0 (car ctx)) ctx)) (a ctx) (b rest))
                 (:instance base-pair (x (car ctx)) (y (find-diff 0 (get3 0 (car ctx)) ctx)))))))

(defthm create-pair
  (implies (and (scheme-p n ctx) (natp n) (<= 2 n) (subsetp-equal ctx rest)
                (rank-one-p n tt))
           (reachable rest (list* tt tt rest)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable reachable-trans reachable-trans-2 steer-all some-pair scheme-p)
           :use (some-pair
                 (:instance steer-all (p (put3 0 (car ctx) (get3 0 (find-diff 0 (get3 0 (car ctx)) ctx)))))
                 (:instance reachable-trans
                            (x rest)
                            (y (list* (put3 0 (car ctx) (get3 0 (find-diff 0 (get3 0 (car ctx)) ctx)))
                                      (put3 0 (car ctx) (get3 0 (find-diff 0 (get3 0 (car ctx)) ctx)))
                                      rest))
                            (z (list* tt tt rest)))))))

;; ===================================================================
;; Part 10.  Pairs for a whole list
;; ===================================================================
(defun dbl (l) (if (consp l) (list* (car l) (car l) (dbl (cdr l))) nil))
(defthm subsetp-append-right
  (implies (subsetp-equal a b) (subsetp-equal a (append c b))))
(defthm create-pairs
  (implies (and (scheme-p n ctx) (natp n) (<= 2 n) (subsetp-equal ctx rest)
                (rank-one-list-p n ts))
           (reachable rest (append (dbl ts) rest)))
  :hints (("Goal" :in-theory (disable scheme-p rank-one-p))
          ("Subgoal *1/2" :in-theory (disable scheme-p rank-one-p reachable-trans create-pair)
           :use ((:instance create-pair (tt (car ts)) (rest (append (dbl (cdr ts)) rest)))
                 (:instance reachable-trans (x rest) (y (append (dbl (cdr ts)) rest))
                            (z (append (dbl ts) rest)))))))

;; ===================================================================
;; Part 11.  Expanding a term into elementary terms
;; ===================================================================
(defthm plus-front-put
  (implies (and (pos-p pos) (good3 tt) (posp s) (posp x)
                (member-equal x (factors-at pos rest))
                (not (equal x s)))
           (reachable (cons (put3 pos tt s) rest)
                      (list* (put3 pos tt (logxor s x)) (put3 pos tt x) rest)))
  :hints (("Goal" :in-theory (e/d (plus-a plus-b) (plus-front))
           :use ((:instance plus-front (v (put3 pos tt s)) (c (find-cat pos x rest)))))))

(defun expand-pos (pos tt is)
  (if (consp is) (cons (put3 pos tt (expt 2 (car is))) (expand-pos pos tt (cdr is))) nil))

(defun nat-dupfree (is)
  (if (consp is) (and (natp (car is)) (not (member-equal (car is) (cdr is))) (nat-dupfree (cdr is))) t))
(defthm logbitp-sume
  (implies (and (natp j) (nat-dupfree is))
           (equal (logbitp j (sume is)) (if (member-equal j is) t nil))))
(defthm sume-nonzero
  (implies (and (nat-dupfree is) (consp is)) (posp (sume is)))
  :hints (("Goal" :in-theory (disable logbitp-sume)
           :use ((:instance logbitp-sume (j (car is)))))))

(defun cats (pos is rest)
  (if (consp is) (and (member-equal (expt 2 (car is)) (factors-at pos rest)) (cats pos (cdr is) rest)) t))
(defthm factors-at-cons-member
  (implies (member-equal x (factors-at pos rest))
           (member-equal x (factors-at pos (cons y rest)))))
(defthm cats-cons (implies (cats pos is rest) (cats pos is (cons y rest))))

(defthm sume-cons-not-equal
  (implies (and (nat-dupfree is) (consp is) (consp (cdr is)))
           (not (equal (expt 2 (car is)) (logxor (expt 2 (car is)) (sume (cdr is))))))
  :hints (("Goal" :in-theory (disable sume-nonzero)
           :use ((:instance sume-nonzero (is (cdr is)))))))

(defthm sume-not-pow
  (implies (and (nat-dupfree is) (natp i) (not (member-equal i is)))
           (not (equal (sume is) (expt 2 i))))
  :hints (("Goal" :in-theory (disable logbitp-sume)
           :use ((:instance logbitp-sume (j i))))))
(defun ex-ind (pos tt is rest)
  (if (and (consp is) (consp (cdr is)))
      (ex-ind pos tt (cdr is) (cons (put3 pos tt (expt 2 (car is))) rest))
    (list pos tt is rest)))
(defthm expand-pos-reach
  (implies (and (pos-p pos) (good3 tt) (nat-dupfree is) (consp is) (cats pos is rest))
           (reachable (cons (put3 pos tt (sume is)) rest)
                      (append (expand-pos pos tt is) rest)))
  :hints (("Goal" :induct (ex-ind pos tt is rest))
          ("Subgoal *1/1" :in-theory (disable reachable-trans plus-front-put)
           :use ((:instance plus-front-put (s (sume is)) (x (expt 2 (car is))))
                 (:instance reachable-trans
                            (x (cons (put3 pos tt (sume is)) rest))
                            (y (list* (put3 pos tt (sume (cdr is))) (put3 pos tt (expt 2 (car is))) rest))
                            (z (append (expand-pos pos tt is) rest)))))))

(defun ex (n pos tt) (expand-pos pos tt (bits-below (sq n) (get3 pos tt))))

(defthm member-all-below
  (implies (and (all-below k xs) (member-equal j xs)) (< j k))
  :rule-classes nil)
(defthm nat-dupfree-bits-below (nat-dupfree (bits-below k p))
  :hints (("Goal" :induct (bits-below k p))
          ("Subgoal *1/2" :use ((:instance member-all-below (k (1- k)) (j (1- k)) (xs (bits-below (1- k) p)))))))
(defthm consp-bits-below
  (implies (and (natp k) (unsigned-byte-p k p) (not (equal p 0)))
           (consp (bits-below k p)))
  :hints (("Goal" :in-theory (disable sume-bits-below)
           :use sume-bits-below)))

(defun cats-upto (pos k rest)
  (if (zp k) t
    (and (member-equal (expt 2 (1- k)) (factors-at pos rest))
         (cats-upto pos (1- k) rest))))
(defthm cats-upto-bits-below
  (implies (cats-upto pos k rest) (cats pos (bits-below k p) rest)))
(defthm factors-at-append
  (equal (factors-at pos (append a b)) (append (factors-at pos a) (factors-at pos b))))
(defthm cats-upto-append
  (implies (cats-upto pos k rest) (cats-upto pos k (append x rest))))
(defthm cats-upto-cons
  (implies (cats-upto pos k rest) (cats-upto pos k (cons y rest))))

(defthm rank-one-get3-nonzero
  (implies (and (rank-one-p n tt) (pos-p pos) (natp n)) (not (equal (get3 pos tt) 0)))
  :hints (("Goal" :in-theory (disable rank-one-p rank-one-facts) :use ((:instance rank-one-facts (x tt))))))
(defthm ex-reach
  (implies (and (pos-p pos) (rank-one-p n tt) (natp n) (cats-upto pos (sq n) rest))
           (reachable (cons tt rest) (append (ex n pos tt) rest)))
  :hints (("Goal" :in-theory (disable expand-pos-reach rank-one-p rank-one-facts)
           :use ((:instance expand-pos-reach (is (bits-below (sq n) (get3 pos tt))))
                 (:instance rank-one-facts (x tt))
                 (:instance consp-bits-below (k (sq n)) (p (get3 pos tt)))))))

(defthm ubp-expt (implies (and (natp k) (natp i) (< i k)) (unsigned-byte-p k (expt 2 i)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))
(defthm rank-one-put3
  (implies (and (rank-one-p n tt) (pos-p pos) (unsigned-byte-p (sq n) v) (posp v))
           (rank-one-p n (put3 pos tt v)))
  :hints (("Goal" :in-theory (enable pos-p put3 update-nth nth)
           :use ((:instance len3-form (x tt))))))
(defthm rank-one-expand-pos
  (implies (and (rank-one-p n tt) (pos-p pos) (natp n) (all-below (sq n) is))
           (rank-one-list-p n (expand-pos pos tt is)))
  :hints (("Goal" :in-theory (disable rank-one-p))))
(defthm rank-one-ex
  (implies (and (rank-one-p n tt) (pos-p pos) (natp n))
           (rank-one-list-p n (ex n pos tt)))
  :hints (("Goal" :in-theory (disable rank-one-p))))
(in-theory (disable ex))

(defun ex-list (n pos x)
  (if (consp x) (append (ex n pos (car x)) (ex-list n pos (cdr x))) nil))
(defthm rank-one-list-append
  (equal (rank-one-list-p n (append a b)) (and (rank-one-list-p n a) (rank-one-list-p n b))))
(defthm rank-one-ex-list
  (implies (and (rank-one-list-p n x) (pos-p pos) (natp n))
           (rank-one-list-p n (ex-list n pos x)))
  :hints (("Goal" :in-theory (disable rank-one-p))))

(defun exl-ind (n pos x rest)
  (if (consp x) (exl-ind n pos (cdr x) (append (ex n pos (car x)) rest)) (list n pos x rest)))
(defthm perm-append-swap (perm (append a (append b c)) (append b (append a c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable perm-necc)
           :use ((:instance perm-necc (a (perm-witness (append a (append b c)) (append b (append a c))))
                            (x (append a (append b c))) (y (append b (append a c))))))))

(defthm ex-list-reach
  (implies (and (pos-p pos) (rank-one-list-p n x) (natp n) (cats-upto pos (sq n) rest))
           (reachable (append x rest) (append (ex-list n pos x) rest)))
  :hints (("Goal" :induct (exl-ind n pos x rest) :in-theory (disable rank-one-p))
          ("Subgoal *1/1" :in-theory (disable rank-one-p reachable-trans reachable-trans-2 ex-reach)
           :use ((:instance ex-reach (tt (car x)) (rest (append (cdr x) rest)))
                 (:instance perm-append-swap (a (ex n pos (car x))) (b (cdr x)) (c rest))
                 (:instance reach-perm2 (a (append x rest))
                            (b (append (ex n pos (car x)) (append (cdr x) rest)))
                            (c (append (cdr x) (append (ex n pos (car x)) rest))))
                 (:instance reachable-trans (x (append x rest))
                            (y (append (cdr x) (append (ex n pos (car x)) rest)))
                            (z (append (ex-list n pos (cdr x)) (append (ex n pos (car x)) rest))))
                 (:instance perm-append-swap (a (ex-list n pos (cdr x))) (b (ex n pos (car x))) (c rest))
                 (:instance reach-perm2 (a (append x rest))
                            (b (append (ex-list n pos (cdr x)) (append (ex n pos (car x)) rest)))
                            (c (append (ex n pos (car x)) (append (ex-list n pos (cdr x)) rest))))))))

;; ===================================================================
;; Part 12.  Full expansion
;; ===================================================================
(defun expand-all (n x) (ex-list n 2 (ex-list n 1 (ex-list n 0 x))))
(defun all-cats (n rest)
  (and (cats-upto 0 (sq n) rest) (cats-upto 1 (sq n) rest) (cats-upto 2 (sq n) rest)))

(defthm expand-all-reach
  (implies (and (rank-one-list-p n x) (natp n) (all-cats n rest))
           (reachable (append x rest) (append (expand-all n x) rest)))
  :hints (("Goal" :in-theory (e/d (pos-p) (ex-list-reach reachable-trans reachable-trans-2 ex-list))
           :use ((:instance ex-list-reach (pos 0))
                 (:instance ex-list-reach (pos 1) (x (ex-list n 0 x)))
                 (:instance ex-list-reach (pos 2) (x (ex-list n 1 (ex-list n 0 x))))
                 (:instance reachable-trans (x (append x rest))
                            (y (append (ex-list n 0 x) rest))
                            (z (append (ex-list n 1 (ex-list n 0 x)) rest)))
                 (:instance reachable-trans (x (append x rest))
                            (y (append (ex-list n 1 (ex-list n 0 x)) rest))
                            (z (append (expand-all n x) rest)))))))

;; tensor entries are invariant under expansion
(defun t1 (x i j k)
  (and (logbitp i (nth 0 x)) (logbitp j (nth 1 x)) (logbitp k (nth 2 x)) t))
(defthm tentry-cons-t1
  (equal (tentry (cons x l) i j k) (xor (t1 x i j k) (tentry l i j k))))
(defthm tentry-nil (equal (tentry nil i j k) nil))
(defthmd tentry-when-consp
  (implies (consp x) (equal (tentry x i j k) (xor (t1 (car x) i j k) (tentry (cdr x) i j k)))))
(defthm tentry-atom (implies (not (consp x)) (equal (tentry x i j k) nil)))
(defthm tentry-append
  (equal (tentry (append a b) i j k) (xor (tentry a i j k) (tentry b i j k))))
(defthm t1-put3-logxor
  (implies (pos-p pos)
           (equal (t1 (put3 pos tt (logxor a b)) i j k)
                  (xor (t1 (put3 pos tt a) i j k) (t1 (put3 pos tt b) i j k))))
  :hints (("Goal" :in-theory (enable pos-p put3))))
(defthm t1-put3-zero
  (implies (pos-p pos) (not (t1 (put3 pos tt 0) i j k)))
  :hints (("Goal" :in-theory (enable pos-p put3))))
(in-theory (disable tentry t1))
(defthm tentry-expand-pos
  (implies (and (pos-p pos) (nat-dupfree is))
           (equal (tentry (expand-pos pos tt is) i j k)
                  (t1 (put3 pos tt (sume is)) i j k))))
(defthm tentry-ex
  (implies (and (pos-p pos) (rank-one-p n tt) (natp n))
           (equal (tentry (ex n pos tt) i j k) (t1 tt i j k)))
  :hints (("Goal" :in-theory (e/d (ex) (rank-one-p)))))
(defthm tentry-ex-list
  (implies (and (pos-p pos) (rank-one-list-p n x) (natp n))
           (equal (tentry (ex-list n pos x) i j k) (tentry x i j k)))
  :hints (("Goal" :in-theory (e/d (tentry-when-consp) (rank-one-p)))))
(defthm tentry-expand-all
  (implies (and (rank-one-list-p n x) (natp n))
           (equal (tentry (expand-all n x) i j k) (tentry x i j k)))
  :hints (("Goal" :in-theory (enable pos-p))))

;; ===================================================================
;; Part 13.  Elementary terms and parity of multiplicities
;; ===================================================================
(defun lg (v) (1- (integer-length v)))
(defun pow2-p (v) (and (natp v) (equal v (expt 2 (lg v)))))
(defthm pow2-p-expt (implies (natp i) (pow2-p (expt 2 i)))
  :hints (("Goal" :in-theory (enable bitops::|(integer-length (expt 2 n))|))))
(defthm lg-expt (implies (natp i) (equal (lg (expt 2 i)) i)))
(defthm natp-lg (implies (pow2-p v) (natp (lg v)))
  :hints (("Goal" :cases ((equal (integer-length v) 0)))))
(in-theory (disable lg))
(defthm expt2-inj
  (implies (and (natp a) (natp b)) (equal (equal (expt 2 a) (expt 2 b)) (equal a b)))
  :hints (("Goal" :in-theory (disable bitops::logbitp-of-expt-2)
           :use ((:instance bitops::logbitp-of-expt-2 (a a) (b b))
                 (:instance bitops::logbitp-of-expt-2 (a a) (b a))))))

(defun elem3-p (x)
  (and (true-listp x) (equal (len x) 3)
       (pow2-p (nth 0 x)) (pow2-p (nth 1 x)) (pow2-p (nth 2 x))))
(defun elem-list-p (l) (if (consp l) (and (elem3-p (car l)) (elem-list-p (cdr l))) t))

(defthm elem3-form
  (implies (elem3-p x)
           (equal (list (expt 2 (lg (nth 0 x))) (expt 2 (lg (nth 1 x))) (expt 2 (lg (nth 2 x)))) x))
  :rule-classes nil
  :hints (("Goal" :use len3-form)))

(defthm t1-explicit
  (implies (and (natp a) (natp b) (natp c) (natp i) (natp j) (natp k))
           (equal (t1 (list (expt 2 a) (expt 2 b) (expt 2 c)) i j k)
                  (equal (list (expt 2 a) (expt 2 b) (expt 2 c))
                         (list (expt 2 i) (expt 2 j) (expt 2 k)))))
  :hints (("Goal" :in-theory (enable t1))))
(defthm t1-elem
  (implies (and (elem3-p x) (natp i) (natp j) (natp k))
           (equal (t1 x i j k) (equal x (list (expt 2 i) (expt 2 j) (expt 2 k)))))
  :hints (("Goal" :in-theory (e/d (elem3-p) (pow2-p t1 t1-explicit))
           :use (elem3-form
                 (:instance t1-explicit (a (lg (nth 0 x))) (b (lg (nth 1 x))) (c (lg (nth 2 x))))
                 (:instance natp-lg (v (nth 0 x))) (:instance natp-lg (v (nth 1 x)))
                 (:instance natp-lg (v (nth 2 x)))))))

(defthm oddp-plus-1
  (implies (natp x) (equal (oddp (+ 1 x)) (not (oddp x))))
  :hints (("Goal" :in-theory (enable oddp evenp))))
(defthm natp-cnt (natp (cnt a x)) :rule-classes :type-prescription)
(defthm tentry-elem
  (implies (and (elem-list-p l) (natp i) (natp j) (natp k))
           (equal (tentry l i j k) (oddp (cnt (list (expt 2 i) (expt 2 j) (expt 2 k)) l))))
  :hints (("Goal" :in-theory (e/d (tentry-when-consp) (elem3-p)))))

;; expansions consist of elementary terms
(defun pow-at (pos l) (if (consp l) (and (pow2-p (get3 pos (car l))) (pow-at pos (cdr l))) t))
(defthm pow-at-expand-pos-same
  (implies (and (pos-p pos) (nat-dupfree is)) (pow-at pos (expand-pos pos tt is))))
(defthm pow-at-expand-pos-other
  (implies (and (pos-p pos) (pos-p q) (not (equal q pos)) (pow2-p (get3 q tt)))
           (pow-at q (expand-pos pos tt is)))
  :hints (("Goal" :in-theory (enable pos-p))))
(defthm pow-at-append (equal (pow-at pos (append a b)) (and (pow-at pos a) (pow-at pos b))))
(defthm pow-at-ex-list-same
  (implies (pos-p pos) (pow-at pos (ex-list n pos x)))
  :hints (("Goal" :in-theory (enable ex))))
(defthm pow-at-ex-list-other
  (implies (and (pos-p pos) (pos-p q) (not (equal q pos)) (pow-at q x))
           (pow-at q (ex-list n pos x)))
  :hints (("Goal" :in-theory (enable ex))))
(defthm elem-from-pow
  (implies (and (rank-one-list-p n l) (natp n) (pow-at 0 l) (pow-at 1 l) (pow-at 2 l))
           (elem-list-p l))
  :hints (("Goal" :in-theory (enable get3))))
(defthm elem-expand-all
  (implies (and (rank-one-list-p n x) (natp n))
           (elem-list-p (expand-all n x)))
  :hints (("Goal" :in-theory (e/d (pos-p) (elem-from-pow))
           :use ((:instance elem-from-pow (l (expand-all n x)))))))

;; ===================================================================
;; Part 14.  Cancelling a list in which every object occurs evenly often
;; ===================================================================
(defthm len-remove1 (<= (len (remove1-equal a x)) (len x)) :rule-classes :linear)
(defun even-counts (z)
  (declare (xargs :measure (len z)))
  (if (consp z)
      (and (member-equal (car z) (cdr z))
           (even-counts (remove1-equal (car z) (cdr z))))
    t))

(defthm perm-pull-pair
  (implies (member-equal a z)
           (perm (cons a (append z r)) (list* a a (append (remove1-equal a z) r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (member-iff-cnt) (perm-necc))
           :use ((:instance perm-necc (a (perm-witness (cons a (append z r))
                                                        (list* a a (append (remove1-equal a z) r))))
                            (x (cons a (append z r)))
                            (y (list* a a (append (remove1-equal a z) r))))))))

(defthm cancel-all
  (implies (even-counts z) (reachable (append z rest) rest))
  :hints (("Goal" :induct (even-counts z))
          ("Subgoal *1/1" :in-theory (disable reachable-trans reachable-trans-2 cancel-front)
           :use ((:instance perm-pull-pair (a (car z)) (z (cdr z)) (r rest))
                 (:instance cancel-front (z (car z)) (rest (append (remove1-equal (car z) (cdr z)) rest)))
                 (:instance reach-perm1
                            (a (list* (car z) (car z) (append (remove1-equal (car z) (cdr z)) rest)))
                            (b (append (remove1-equal (car z) (cdr z)) rest))
                            (c (cons (car z) (append (cdr z) rest))))
                 (:instance reachable-trans
                            (x (cons (car z) (append (cdr z) rest)))
                            (y (append (remove1-equal (car z) (cdr z)) rest))
                            (z rest))))))

(defthm cnt-non-member (implies (not (member-equal a x)) (equal (cnt a x) 0)))
(defun all-even (w z) (if (consp w) (and (evenp (cnt (car w) z)) (all-even (cdr w) z)) t))
(defthm all-even-member
  (implies (and (all-even w z) (member-equal a w)) (evenp (cnt a z))))
(defthm all-even-remove-pair
  (implies (and (all-even w z) (consp z))
           (all-even w (remove1-equal (car z) (cdr z))))
  :hints (("Goal" :in-theory (enable evenp))))
(defthm even-cnt-member
  (implies (and (consp z) (evenp (cnt (car z) z))) (member-equal (car z) (cdr z)))
  :hints (("Goal" :in-theory (enable member-iff-cnt evenp))))
(defthm subsetp-remove1
  (implies (subsetp-equal x w) (subsetp-equal (remove1-equal a x) w)))
(defthm all-even-implies-even-counts
  (implies (and (subsetp-equal z w) (all-even w z)) (even-counts z))
  :hints (("Goal" :induct (even-counts z))
          ("Subgoal *1/2" :use ((:instance all-even-member (a (car z)))))))

(defthm evenp-sum-same-parity
  (implies (and (natp a) (natp b) (equal (oddp a) (oddp b))) (evenp (+ a b)))
  :hints (("Goal" :in-theory (enable oddp evenp))))
(defthm even-cnt-helper
  (implies (and (elem-list-p e1) (elem-list-p e2) (natp i) (natp j) (natp k)
                (equal (tentry e1 i j k) (tentry e2 i j k)))
           (evenp (+ (cnt (list (expt 2 i) (expt 2 j) (expt 2 k)) e1)
                     (cnt (list (expt 2 i) (expt 2 j) (expt 2 k)) e2))))
  :hints (("Goal" :in-theory (disable tentry-elem)
           :use ((:instance tentry-elem (l e1)) (:instance tentry-elem (l e2))))))
(defthm elem-list-member (implies (and (elem-list-p l) (member-equal a l)) (elem3-p a)))
(defthm rank-one-list-member (implies (and (rank-one-list-p n l) (member-equal a l)) (rank-one-p n a)))
(defthm elem-list-append (equal (elem-list-p (append a b)) (and (elem-list-p a) (elem-list-p b))))
(defthm ubp-expt-bound
  (implies (and (natp i) (natp k) (unsigned-byte-p k (expt 2 i))) (< i k))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable unsigned-byte-p)
           :cases ((<= k i)))
          ("Subgoal 1" :use ((:instance (:theorem (implies (and (natp k) (natp i) (<= k i)) (<= (expt 2 k) (expt 2 i)))))))))

(defthm pow2-expt-lg (implies (pow2-p v) (equal (expt 2 (lg v)) v)))
(defthm lg-bound
  (implies (and (pow2-p v) (unsigned-byte-p k v) (natp k)) (< (lg v) k))
  :hints (("Goal" :in-theory (disable pow2-p)
           :use ((:instance ubp-expt-bound (i (lg v)))
                 (:instance natp-lg)))))
(defthm elem-index-bounds
  (implies (and (elem3-p a) (rank-one-p n a) (natp n))
           (and (< (lg (nth 0 a)) (sq n)) (< (lg (nth 1 a)) (sq n)) (< (lg (nth 2 a)) (sq n))))
  :hints (("Goal" :in-theory (enable rank-one-p))))

(defthm rank-one-expand-all
  (implies (and (rank-one-list-p n x) (natp n)) (rank-one-list-p n (expand-all n x)))
  :hints (("Goal" :in-theory (enable pos-p))))
(defthm elem3-facts
  (implies (elem3-p a)
           (and (natp (lg (nth 0 a))) (natp (lg (nth 1 a))) (natp (lg (nth 2 a)))))
  :hints (("Goal" :in-theory (disable pow2-p))))
(defthm even-cnt-helper2
  (implies (and (elem-list-p e1) (elem-list-p e2) (natp i) (natp j) (natp k)
                (equal a (list (expt 2 i) (expt 2 j) (expt 2 k)))
                (equal (tentry e1 i j k) (tentry e2 i j k)))
           (evenp (+ (cnt a e1) (cnt a e2))))
  :rule-classes nil
  :hints (("Goal" :use even-cnt-helper)))
(defthm even-cnt-elem
  (implies (and (scheme-p n x) (scheme-p n e2) (elem-list-p e2) (posp n)
                (member-equal a (append (expand-all n x) e2)))
           (evenp (cnt a (append (expand-all n x) e2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (even-cnt-helper scheme-tentry elem-index-bounds elem3-p scheme-p
                               expand-all tentry-elem rank-one-p pow2-p elem3-facts))
           :use ((:instance elem3-form (x a))
                 (:instance elem3-facts)
                 (:instance elem-list-member (l (append (expand-all n x) e2)))
                 (:instance rank-one-list-member (l (append (expand-all n x) e2)))
                 (:instance elem-index-bounds)
                 (:instance even-cnt-helper2 (e1 (expand-all n x)) (i (lg (nth 0 a))) (j (lg (nth 1 a))) (k (lg (nth 2 a))))
                 (:instance scheme-tentry (s x) (a (lg (nth 0 a))) (b (lg (nth 1 a))) (c (lg (nth 2 a))))
                 (:instance scheme-tentry (s e2) (a (lg (nth 0 a))) (b (lg (nth 1 a))) (c (lg (nth 2 a))))))))

(defun cdr-ind (w) (if (consp w) (cdr-ind (cdr w)) nil))
(defthm all-even-elem
  (implies (and (scheme-p n x) (scheme-p n e2) (elem-list-p e2) (posp n)
                (subsetp-equal w (append (expand-all n x) e2)))
           (all-even w (append (expand-all n x) e2)))
  :hints (("Goal" :induct (cdr-ind w) :in-theory (disable scheme-p expand-all even-cnt-elem))
          ("Subgoal *1/1" :use ((:instance even-cnt-elem (a (car w)))))))

(defthm subsetp-cons-right (implies (subsetp-equal x y) (subsetp-equal x (cons a y))))
(defthm subsetp-refl (subsetp-equal x x))
(defthm even-counts-elem
  (implies (and (scheme-p n x) (scheme-p n e2) (elem-list-p e2) (posp n))
           (even-counts (append (expand-all n x) e2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable scheme-p expand-all all-even-implies-even-counts)
           :use ((:instance all-even-implies-even-counts
                            (z (append (expand-all n x) e2)) (w (append (expand-all n x) e2)))))))

;; ===================================================================
;; Part 15.  The standard scheme S0 (all elementary E_kh (x) E_hl (x) E_kl)
;; ===================================================================
(defun s0c (n a b c)
  (if (zp c) nil
    (if (mflat n a b (1- c))
        (cons (list (expt 2 a) (expt 2 b) (expt 2 (1- c))) (s0c n a b (1- c)))
      (s0c n a b (1- c)))))
(defun s0b (n a b k)
  (if (zp b) nil (append (s0c n a (1- b) k) (s0b n a (1- b) k))))
(defun s0a (n a k)
  (if (zp a) nil (append (s0b n (1- a) k k) (s0a n (1- a) k))))
(defun std-scheme (n) (s0a n (sq n) (sq n)))

(defthm tentry-s0c
  (implies (and (natp a) (natp b) (natp i) (natp j) (natp k))
           (equal (tentry (s0c n a b c) i j k)
                  (and (equal i a) (equal j b) (< k (nfix c)) (mflat n i j k))))
  :hints (("Goal" :induct (s0c n a b c))))
(defthm tentry-s0b
  (implies (and (natp a) (natp i) (natp j) (natp k))
           (equal (tentry (s0b n a b c) i j k)
                  (and (equal i a) (< j (nfix b)) (< k (nfix c)) (mflat n i j k))))
  :hints (("Goal" :induct (s0b n a b c))))
(defthm tentry-s0a
  (implies (and (natp i) (natp j) (natp k))
           (equal (tentry (s0a n a c) i j k)
                  (and (< i (nfix a)) (< j (nfix c)) (< k (nfix c)) (mflat n i j k))))
  :hints (("Goal" :induct (s0a n a c))))

(defthm rank-one-elem
  (implies (and (natp a) (natp b) (natp c) (natp n) (< a (sq n)) (< b (sq n)) (< c (sq n)))
           (rank-one-p n (list (expt 2 a) (expt 2 b) (expt 2 c))))
  :hints (("Goal" :in-theory (enable rank-one-p))))
(defthm elem3-elem
  (implies (and (natp a) (natp b) (natp c))
           (elem3-p (list (expt 2 a) (expt 2 b) (expt 2 c)))))
(in-theory (disable elem3-p))
(defthm s0c-props
  (implies (and (natp a) (natp b) (natp n) (< a (sq n)) (< b (sq n)) (<= (nfix c) (sq n)))
           (and (elem-list-p (s0c n a b c)) (rank-one-list-p n (s0c n a b c))
                (true-listp (s0c n a b c))))
  :hints (("Goal" :induct (s0c n a b c) :in-theory (disable rank-one-p))))
(defthm s0b-props
  (implies (and (natp a) (natp n) (< a (sq n)) (<= (nfix b) (sq n)) (equal c (sq n)))
           (and (elem-list-p (s0b n a b c)) (rank-one-list-p n (s0b n a b c))
                (true-listp (s0b n a b c))))
  :hints (("Goal" :induct (s0b n a b c) :in-theory (disable rank-one-p))))
(defthm s0a-props
  (implies (and (natp n) (<= (nfix a) (sq n)) (equal c (sq n)))
           (and (elem-list-p (s0a n a c)) (rank-one-list-p n (s0a n a c))
                (true-listp (s0a n a c))))
  :hints (("Goal" :induct (s0a n a c) :in-theory (disable rank-one-p))))

(defthm floor-flat (implies (and (natp g) (natp h) (posp n) (< h n)) (equal (floor (+ h (* g n)) n) g)))
(defthm mod-flat (implies (and (natp g) (natp h) (posp n) (< h n)) (equal (mod (+ h (* g n)) n) h)))
(defthm flat-bound (implies (and (natp g) (natp h) (posp n) (< h n) (< g n)) (< (+ h (* g n)) (* n n)))
  :hints (("Goal" :nonlinearp t)))

(defthm flat-bound-sq (implies (and (natp g) (natp h) (posp n) (< h n) (< g n)) (< (+ h (* g n)) (sq n)))
  :hints (("Goal" :in-theory (enable sq) :nonlinearp t)))
(defthm std-sum-entry
  (implies (and (posp n) (idx-p n g) (idx-p n h) (idx-p n i) (idx-p n j) (idx-p n k) (idx-p n l))
           (equal (sum-entry n (std-scheme n) g h i j k l) (mm-entry g h i j k l)))
  :hints (("Goal" :in-theory (enable mflat))))
(defthm std-props
  (implies (natp n)
           (and (elem-list-p (std-scheme n)) (rank-one-list-p n (std-scheme n))
                (true-listp (std-scheme n)))))
(defthm std-scheme-p
  (implies (posp n) (scheme-p n (std-scheme n)))
  :hints (("Goal" :in-theory (e/d (sum-is-mm) (std-scheme std-sum-entry))
           :use ((:instance std-sum-entry
                            (g (mv-nth 0 (sum-is-mm-witness n (std-scheme n))))
                            (h (mv-nth 1 (sum-is-mm-witness n (std-scheme n))))
                            (i (mv-nth 2 (sum-is-mm-witness n (std-scheme n))))
                            (j (mv-nth 3 (sum-is-mm-witness n (std-scheme n))))
                            (k (mv-nth 4 (sum-is-mm-witness n (std-scheme n))))
                            (l (mv-nth 5 (sum-is-mm-witness n (std-scheme n)))))))))

(defthm std-member
  (implies (and (natp n) (natp a) (natp b) (natp c) (< a (sq n)) (< b (sq n)) (< c (sq n))
                (mflat n a b c))
           (member-equal (list (expt 2 a) (expt 2 b) (expt 2 c)) (std-scheme n)))
  :hints (("Goal" :in-theory (e/d (member-iff-cnt std-scheme) (tentry-elem tentry-s0a))
           :use ((:instance tentry-elem (l (std-scheme n)) (i a) (j b) (k c))
                 (:instance tentry-s0a (a (sq n)) (c (sq n)) (i a) (j b) (k c))))))

(defthm sq-bounds
  (implies (and (natp x) (posp n) (< x (sq n)))
           (and (< (* n (mod x n)) (sq n)) (< (* n (floor x n)) (sq n))
                (< (mod x n) (sq n)) (< (floor x n) (sq n))))
  :hints (("Goal" :in-theory (enable sq) :nonlinearp t)))

(defthm std-cat
  (implies (and (posp n) (natp x) (< x (sq n)) (pos-p pos))
           (member-equal (expt 2 x) (factors-at pos (std-scheme n))))
  :hints (("Goal" :in-theory (e/d (pos-p get3) (std-member member-factors-at std-scheme))
           :use ((:instance std-member (a x) (b (* n (mod x n))) (c (* n (floor x n))))
                 (:instance std-member (b x) (a (floor x n)) (c (mod x n)))
                 (:instance std-member (c x) (a (* n (floor x n))) (b (mod x n)))
                 (:instance member-factors-at (pos 0) (rest (std-scheme n))
                            (x (list (expt 2 x) (expt 2 (* n (mod x n))) (expt 2 (* n (floor x n))))))
                 (:instance member-factors-at (pos 1) (rest (std-scheme n))
                            (x (list (expt 2 (floor x n)) (expt 2 x) (expt 2 (mod x n)))))
                 (:instance member-factors-at (pos 2) (rest (std-scheme n))
                            (x (list (expt 2 (* n (floor x n))) (expt 2 (mod x n)) (expt 2 x))))))))

(defthm std-cats-upto
  (implies (and (posp n) (pos-p pos) (natp k) (<= k (sq n)))
           (cats-upto pos k (std-scheme n)))
  :hints (("Goal" :in-theory (disable std-scheme))))
(defthm std-all-cats
  (implies (posp n) (all-cats n (std-scheme n)))
  :hints (("Goal" :in-theory (e/d (pos-p) (std-scheme)))))
(in-theory (disable std-scheme all-cats expand-all))

;; ===================================================================
;; Part 17.  Flip and plus transformations map schemes to schemes
;; ===================================================================
(defthm t1-zero-term (implies (zero-term-p x) (not (t1 x i j k)))
  :hints (("Goal" :in-theory (enable t1))))
(defthm tentry-remove-zero-terms
  (equal (tentry (remove-zero-terms l) i j k) (tentry l i j k))
  :hints (("Goal" :in-theory (enable tentry-when-consp))))
(defthm tentry-remove1
  (implies (member-equal u s)
           (equal (tentry (remove1-equal u s) i j k) (xor (t1 u i j k) (tentry s i j k))))
  :hints (("Goal" :in-theory (enable tentry-when-consp))))

(defun term3-p (x) (and (true-listp x) (equal (len x) 3)
                        (integerp (nth 0 x)) (integerp (nth 1 x)) (integerp (nth 2 x))))
(defthm term3-integer-get3 (implies (and (term3-p x) (pos-p pos)) (integerp (get3 pos x)))
  :hints (("Goal" :in-theory (enable pos-p get3))))
(defthm put3-get3-term3
  (implies (and (term3-p x) (pos-p pos)) (equal (put3 pos x (get3 pos x)) x))
  :hints (("Goal" :in-theory (enable pos-p put3 get3 update-nth nth) :use len3-form)))
(defthm t1-put3-xor-self
  (implies (and (term3-p x) (pos-p pos))
           (equal (t1 (put3 pos x (logxor (get3 pos x) w)) i j k)
                  (xor (t1 x i j k) (t1 (put3 pos x w) i j k))))
  :hints (("Goal" :in-theory (disable t1-put3-logxor put3-get3-term3)
           :use ((:instance t1-put3-logxor (tt x) (a (get3 pos x)) (b w))
                 put3-get3-term3))))
(defthm flip-cross-equal
  (implies (and (term3-p u) (term3-p v) (pos-p pos) (equal (get3 pos u) (get3 pos v)))
           (equal (put3 (flip-q pos) u (get3 (flip-q pos) v))
                  (put3 (flip-r pos) v (get3 (flip-r pos) u))))
  :hints (("Goal" :in-theory (enable pos-p put3 get3 update-nth nth)
           :use (len3-form (:instance len3-form (x v)) (:instance len3-form (x u))))))
(defthm flip-q-r-pos
  (implies (pos-p pos) (and (pos-p (flip-q pos)) (pos-p (flip-r pos))))
  :hints (("Goal" :in-theory (enable pos-p))))
(in-theory (disable flip-q flip-r))

(defthm move-member-u (implies (move-valid-p m s) (member-equal (mv-u m) s))
  :hints (("Goal" :in-theory (enable move-valid-p))))
(defthm move-member-v (implies (move-valid-p m s) (member-equal (mv-v m) s))
  :hints (("Goal" :in-theory (enable move-valid-p))))

(defthm move-member-v2
  (implies (move-valid-p m s) (member-equal (mv-v m) (remove1-equal (mv-u m) s)))
  :hints (("Goal" :in-theory (enable move-valid-p))))
(defthm move-pos-ok (implies (move-valid-p m s) (pos-p (mv-pos m)))
  :hints (("Goal" :in-theory (enable move-valid-p pos-p))))
(in-theory (disable remove-zero-terms zero-term-p))
(defthm move-flip-equal
  (implies (and (move-valid-p m s) (equal (mv-kind m) :flip))
           (equal (get3 (mv-pos m) (mv-u m)) (get3 (mv-pos m) (mv-v m))))
  :hints (("Goal" :in-theory (enable move-valid-p))))
(defthm tentry-plus-results
  (implies (and (term3-p v) (term3-p u) (pos-p pos))
           (equal (tentry (plus-results pos u v) i j k) (t1 v i j k)))
  :hints (("Goal" :in-theory (enable plus-results))))
(defthm tentry-flip-results
  (implies (and (term3-p u) (term3-p v) (pos-p pos) (equal (get3 pos u) (get3 pos v)))
           (equal (tentry (flip-results pos u v) i j k) (xor (t1 u i j k) (t1 v i j k))))
  :hints (("Goal" :in-theory (e/d (flip-results) (flip-cross-equal))
           :use ((:instance flip-cross-equal)))))
(in-theory (disable plus-results flip-results))
(defthm member-remove1-member
  (implies (member-equal v (remove1-equal u s)) (member-equal v s)))
(defthm tentry-move
  (implies (and (move-valid-p m s) (term3-p (mv-u m)) (term3-p (mv-v m)))
           (equal (tentry (apply-move m s) i j k) (tentry s i j k)))
  :hints (("Goal" :in-theory (e/d (apply-move move-results move-removed)
                                  (move-valid-p mv-u mv-v mv-pos mv-kind))
           :use ((:instance move-member-u) (:instance move-member-v) (:instance move-pos-ok)
                 (:instance move-member-v2)
                 (:instance move-flip-equal)))))

;; well-formedness is preserved
(defun term-list-p (n l) (if (consp l) (and (term-p n (car l)) (term-list-p n (cdr l))) t))
(defthm rank-one-list-remove-zero
  (implies (term-list-p n l) (rank-one-list-p n (remove-zero-terms l)))
  :hints (("Goal" :in-theory (e/d (remove-zero-terms) (term-p)))))
(defthm rank-one-list-remove1
  (implies (rank-one-list-p n s) (rank-one-list-p n (remove1-equal u s))))
(defthm true-listp-remove1 (implies (true-listp s) (true-listp (remove1-equal u s))))
(defthm rank-one-list-member-term
  (implies (and (rank-one-list-p n s) (member-equal u s)) (term-p n u))
  :hints (("Goal" :in-theory (disable term-p))))
(defthm term-p-term3 (implies (term-p n u) (term3-p u)))
(defthm term-p-put3
  (implies (and (term-p n u) (pos-p pos) (matrix-p n w)) (term-p n (put3 pos u w)))
  :hints (("Goal" :in-theory (e/d (pos-p put3 update-nth nth) (matrix-p))
           :use ((:instance len3-form (x u))))))
(defthm matrix-p-get3
  (implies (and (term-p n u) (pos-p pos)) (matrix-p n (get3 pos u)))
  :hints (("Goal" :in-theory (e/d (pos-p get3) (matrix-p)))))
(defthm matrix-p-logxor
  (implies (and (matrix-p n a) (matrix-p n b)) (matrix-p n (logxor a b))))
(defthm term-list-plus-results
  (implies (and (term-p n u) (term-p n v) (pos-p pos))
           (term-list-p n (plus-results pos u v)))
  :hints (("Goal" :in-theory (e/d (plus-results) (term-p matrix-p)))))
(defthm term-list-flip-results
  (implies (and (term-p n u) (term-p n v) (pos-p pos))
           (term-list-p n (flip-results pos u v)))
  :hints (("Goal" :in-theory (e/d (flip-results) (term-p matrix-p)))))
(in-theory (disable term-p matrix-p term3-p))

(defthm move-preserves-rank-one
  (implies (and (natp n) (rank-one-list-p n s) (true-listp s) (move-valid-p m s))
           (and (rank-one-list-p n (apply-move m s)) (true-listp (apply-move m s))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (apply-move move-results move-removed)
                           (rank-one-list-p remove-zero-terms move-valid-p mv-u mv-v mv-pos mv-kind))
           :use ((:instance move-member-u) (:instance move-member-v)
                 (:instance move-pos-ok)))))

(defthm move-preserves-sum
  (implies (and (sum-is-mm n s) (posp n) (rank-one-list-p n s) (move-valid-p m s))
           (sum-is-mm n (apply-move m s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (sum-is-mm-necc tentry-move move-valid-p))
           :expand ((sum-is-mm n (apply-move m s)))
           :use ((:instance sum-is-mm-necc
                            (g (mv-nth 0 (sum-is-mm-witness n (apply-move m s))))
                            (h (mv-nth 1 (sum-is-mm-witness n (apply-move m s))))
                            (i (mv-nth 2 (sum-is-mm-witness n (apply-move m s))))
                            (j (mv-nth 3 (sum-is-mm-witness n (apply-move m s))))
                            (k (mv-nth 4 (sum-is-mm-witness n (apply-move m s))))
                            (l (mv-nth 5 (sum-is-mm-witness n (apply-move m s)))))
                 (:instance tentry-move
                            (i (+ (* (mv-nth 0 (sum-is-mm-witness n (apply-move m s))) n)
                                  (mv-nth 1 (sum-is-mm-witness n (apply-move m s)))))
                            (j (+ (* (mv-nth 2 (sum-is-mm-witness n (apply-move m s))) n)
                                  (mv-nth 3 (sum-is-mm-witness n (apply-move m s)))))
                            (k (+ (* (mv-nth 4 (sum-is-mm-witness n (apply-move m s))) n)
                                  (mv-nth 5 (sum-is-mm-witness n (apply-move m s))))))
                 (:instance rank-one-list-member-term (u (mv-u m)))
                 (:instance rank-one-list-member-term (u (mv-v m)))
                 (:instance move-member-u) (:instance move-member-v)))))

(defthm move-preserves-scheme
  (implies (and (scheme-p n s) (posp n) (move-valid-p m s))
           (scheme-p n (apply-move m s)))
  :hints (("Goal" :in-theory (disable move-preserves-sum move-preserves-rank-one)
           :use (move-preserves-sum move-preserves-rank-one))))

;; ===================================================================
;; Part 16.  Main argument
;; ===================================================================
(defthm member-factors-append-left
  (implies (member-equal x (factors-at pos a)) (member-equal x (factors-at pos (append a b)))))
(defthm cats-upto-append-left
  (implies (cats-upto pos k a) (cats-upto pos k (append a b))))
(defthm all-cats-append-left
  (implies (all-cats n a) (all-cats n (append a b)))
  :hints (("Goal" :in-theory (enable all-cats))))

(defthm collapse
  (implies (and (scheme-p n x) (posp n))
           (reachable (append x (append (std-scheme n) r)) r))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable scheme-p reachable-trans reachable-trans-2 expand-all-reach cancel-all
                               even-counts-elem)
           :use ((:instance expand-all-reach (rest (append (std-scheme n) r)))
                 (:instance even-counts-elem (e2 (std-scheme n)))
                 (:instance cancel-all (z (append (expand-all n x) (std-scheme n))) (rest r))
                 (:instance reachable-trans
                            (x (append x (append (std-scheme n) r)))
                            (y (append (expand-all n x) (append (std-scheme n) r)))
                            (z r))))))

(defthm cnt-dbl (equal (cnt a (dbl l)) (* 2 (cnt a l))))
(defmacro def-perm-cnt (name x y)
  `(defthm ,name (perm ,x ,y)
     :rule-classes nil
     :hints (("Goal" :in-theory (e/d (perm) (perm-necc))
              :use ((:instance perm-necc (a (perm-witness ,x ,y)) (x ,x) (y ,y)))))))
(def-perm-cnt perm-dbl1 (append (dbl l) r) (append r (append l l)))
(def-perm-cnt perm-dbl2 (append (dbl l) r) (append l (append r l)))

(defthm to-std
  (implies (and (scheme-p n s) (natp n) (<= 2 n))
           (reachable s (std-scheme n)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable scheme-p reachable-trans reachable-trans-2 create-pairs collapse)
           :use ((:instance create-pairs (ctx s) (rest s) (ts (std-scheme n)))
                 (:instance perm-dbl1 (l (std-scheme n)) (r s))
                 (:instance reach-perm2 (a s) (b (append (dbl (std-scheme n)) s))
                            (c (append s (append (std-scheme n) (std-scheme n)))))
                 (:instance collapse (x s) (r (std-scheme n)))
                 (:instance reachable-trans (x s)
                            (y (append s (append (std-scheme n) (std-scheme n))))
                            (z (std-scheme n)))))))

(defthm from-std
  (implies (and (scheme-p n s) (natp n) (<= 2 n))
           (reachable (std-scheme n) s))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable scheme-p reachable-trans reachable-trans-2 create-pairs collapse)
           :use ((:instance create-pairs (ctx (std-scheme n)) (rest (std-scheme n)) (ts s))
                 (:instance perm-dbl2 (l s) (r (std-scheme n)))
                 (:instance reach-perm2 (a (std-scheme n)) (b (append (dbl s) (std-scheme n)))
                            (c (append s (append (std-scheme n) s))))
                 (:instance collapse (x s) (r s))
                 (:instance reachable-trans (x (std-scheme n))
                            (y (append s (append (std-scheme n) s)))
                            (z s))))))

(defthm main-reach
  (implies (and (natp n) (<= 2 n) (scheme-p n s1) (scheme-p n s2))
           (reachable s1 s2))
  :hints (("Goal" :in-theory (disable scheme-p reachable-trans reachable-trans-2 to-std from-std)
           :use ((:instance to-std (s s1)) (:instance from-std (s s2))
                 (:instance reachable-trans (x s1) (y (std-scheme n)) (z s2))))))

;; ===================================================================
;; Sanity check: M(n) satisfies its defining property
;;   (DF)_{k,l} = sum_{g,h,i,j} M(n)_{g,h,i,j,k,l} D_{g,h} F_{i,j}   (over F2)
;; ===================================================================
(encapsulate ()
(defun prod-sum (n d f k l h0)      ; sum_{h<h0} D_{k,h} F_{h,l}
  (if (zp h0) nil
    (xor (and (mentry n d k (1- h0)) (mentry n f (1- h0) l))
         (prod-sum n d f k l (1- h0)))))
(defun mat-prod-entry (n d f k l) (prod-sum n d f k l n))   ; (DF)_{k,l}

(defun mterm (n d f g h i j k l)
  (and (mm-entry g h i j k l) (mentry n d g h) (mentry n f i j)))
(defun sum-j (n d f g h i k l j0)
  (if (zp j0) nil (xor (mterm n d f g h i (1- j0) k l) (sum-j n d f g h i k l (1- j0)))))
(defun sum-i (n d f g h k l i0)
  (if (zp i0) nil (xor (sum-j n d f g h (1- i0) k l n) (sum-i n d f g h k l (1- i0)))))
(defun sum-h (n d f g k l h0)
  (if (zp h0) nil (xor (sum-i n d f g (1- h0) k l n) (sum-h n d f g k l (1- h0)))))
(defun sum-g (n d f k l g0)
  (if (zp g0) nil (xor (sum-h n d f (1- g0) k l n) (sum-g n d f k l (1- g0)))))
(defun mm-sum (n d f k l) (sum-g n d f k l n))   ; sum_{g,h,i,j<n} M D F

(local (in-theory (disable mentry)))
(local (defthm sum-j-val
  (implies (and (natp l) (natp j0) (natp n))
           (equal (sum-j n d f g h i k l j0)
                  (and (< l j0) (equal g k) (equal h i) (mentry n d g h) (mentry n f i l) t)))))
(local (defthm sum-i-val
  (implies (and (natp l) (< l n) (natp h) (natp i0) (natp n))
           (equal (sum-i n d f g h k l i0)
                  (and (< h i0) (equal g k) (mentry n d g h) (mentry n f h l) t)))))
(local (defthm sum-h-val
  (implies (and (natp l) (< l n) (natp h0) (natp n) (<= h0 n))
           (equal (sum-h n d f g k l h0)
                  (and (equal g k) (prod-sum n d f k l h0) t)))))
(local (defthm sum-g-val
  (implies (and (natp k) (natp l) (< l n) (natp g0) (natp n))
           (equal (sum-g n d f k l g0)
                  (and (< k g0) (prod-sum n d f k l n) t)))))
(defthm mm-tensor-correct
  (implies (and (natp n) (idx-p n k) (idx-p n l))
           (iff (mat-prod-entry n d f k l) (mm-sum n d f k l)))))

;; ===================================================================
;; Part 18.  The theorem
;; ===================================================================
(defthm valid-moves-scheme-path
  (implies (and (scheme-p n s) (posp n) (valid-moves-p moves s))
           (scheme-path-p n moves s))
  :hints (("Goal" :induct (run-moves moves s)
           :in-theory (disable scheme-p))))

;; Over F2, for every n >= 2, for any two schemes S1, S2 for M(n) there is a
;; directed path from S1 to S2 in the flip graph whose edges are the flip and
;; plus transformations.
(defthm main
  (implies (and (natp n) (<= 2 n) (scheme-p n s1) (scheme-p n s2))
           (flip-graph-path n s1 s2))
  :hints (("Goal" :in-theory (e/d (reachable) (scheme-p main-reach flip-graph-path-suff))
           :use (main-reach
                 (:instance valid-moves-scheme-path (s s1) (moves (reachable-witness s1 s2)))
                 (:instance flip-graph-path-suff (s s1) (s2 s2) (moves (reachable-witness s1 s2)))))))
