(in-package "ZF")

(include-book "defs")

;;; ============================================================
;;; Part 1: the rationals form a field (theorem rationals-form-field)
;;; ============================================================

(defun q-add2 (x) (+ (rfix (car x)) (rfix (cdr x))))
(defun q-mul2 (x) (* (rfix (car x)) (rfix (cdr x))))
(defun q-neg1 (x) (- (rfix x)))
(defun q-inv1 (x) (/ (rfix x)))
(zify q+ q-add2 :dom (prod2 (rationals) (rationals)) :ran (rationals)
      :props (v$prop rationals$prop))
(zify q* q-mul2 :dom (prod2 (rationals) (rationals)) :ran (rationals)
      :props (v$prop rationals$prop))
(zify q- q-neg1 :dom (rationals) :ran (rationals)
      :props (v$prop rationals$prop))
(zify q/ q-inv1 :dom (nonzeros (rationals) 0) :ran (rationals)
      :props (v$prop rationals$prop diff$prop))

(defthm q-commutativity-2-of-*
  (equal (* x (* y z)) (* y (* x z)))
  :hints (("Goal" :use ((:instance associativity-of-* (x x) (y y) (z z))
                        (:instance associativity-of-* (x y) (y x) (z z)))
                  :in-theory (disable associativity-of-*))))
(defthmz in-singleton
  (equal (in x (singleton a)) (equal x a)))
(defthmz in-nonzeros
  (equal (in x (nonzeros s z)) (and (in x s) (not (equal x z))))
  :props (zfc diff$prop))
(in-theory (disable singleton (:e singleton) prod2-distributes-over-diff nonzeros))

(defthmz q-abelian-group
  (abelian-group-p (rationals) (q+) 0 (q-))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q+$prop q-$prop))
(defthmz q-mul-image
  (subset (image (q*)) (rationals))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop))
(defthmz q-mul-abelian
  (abelian-p (rationals) (q*))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop))
(defthmz q-distributive
  (distributive-p (rationals) (q+) (q*))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop q+$prop))
(defthmz q-minus-one
  (minus-one-not-square (rationals) (q*) (q-) 1)
  :hints (("Goal" :in-theory (disable equal-apply)))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop q-$prop))
(defthmz q-standard
  (rational-ops-standard (q+) (q*))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop q+$prop))

(defthmz subset-prod2-mono
  (implies (and (subset a c) (subset b d))
           (subset (prod2 a b) (prod2 c d)))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz subset-nonzeros
  (subset (nonzeros s z) s)
  :hints (("Goal" :expand ((subset (nonzeros s z) s))))
  :props (zfc diff$prop))
(defthmz q-apply-restrict-prod2
  (implies (and (funp f) (subset (prod2 a b) (domain f)) (in x a) (in y b))
           (equal (apply (restrict f (prod2 a b)) (cons x y))
                  (apply f (cons x y))))
  :props (zfc prod2$prop domain$prop restrict$prop diff$prop))
(defthmz q-nonzero-domain
  (equal (domain (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))))
         (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0)))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop diff$prop restrict$prop))
(defthmz q-nonzero-image
  (subset (image (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))))
          (nonzeros (rationals) 0))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop diff$prop restrict$prop))
(defthmz q-nonzero-group
  (abelian-group-p (nonzeros (rationals) 0) (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))) 1 (q/))
  :hints (("Goal" :in-theory (e/d (in-image-rewrite) (equal-apply apply-restrict))))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop q*$prop q/$prop diff$prop restrict$prop))
(defthmz q-fieldp
  (fieldp (rationals) (q+) (q*) 0 1 (q-) (q/))
  :hints (("Goal" :in-theory (union-theories '(fieldp q-nonzero-group q-abelian-group q-mul-abelian
                q-distributive q-mul-image domain-q* funp-q* funp-q+ funp-q- funp-q/ zify-prop)
              (theory 'minimal-theory))))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop
              q+$prop q*$prop q-$prop q/$prop diff$prop restrict$prop))
(defthmz rationals-form-field (rationals-field-witness)
  :hints (("Goal" :use ((:instance rationals-field-witness-suff
                                   (add (q+)) (mul (q*)) (neg (q-)) (recip (q/))))
           :in-theory (union-theories '(q-fieldp q-minus-one q-standard) (theory 'minimal-theory))))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop
              q+$prop q*$prop q-$prop q/$prop diff$prop restrict$prop))

;;; ============================================================
;;; Part 2: generic development over an abstract field, then the complex
;;; construction (theorems complex-i-squared and complex-construction-is-field)
;;; ============================================================

(in-theory (disable apply2))

(defthmz apply-restrict-prod2
  (implies (and (funp f) (subset (prod2 a b) (domain f)) (in x a) (in y b))
           (equal (apply2 (restrict f (prod2 a b)) x y)
                  (apply2 f x y)))
  :hints (("Goal" :in-theory (enable apply2)))
  :props (zfc prod2$prop domain$prop restrict$prop diff$prop))

;;; Generic functional relation defined by zsub
(encapsulate
  (((gprop) => *) ((gdom) => *) ((gran) => *) ((grel) => *) ((gfn *) => *))
  (local (defun gprop () nil))
  (local (defun gdom () 0))
  (local (defun gran () 0))
  (local (defun grel () 0))
  (local (defun gfn (x) x))
  (defthm gfn-in-gran
    (implies (and (gprop) (in x (gdom)))
             (in (gfn x) (gran))))
  (defthm grel-comprehension
    (implies (gprop)
             (equal (in p (grel))
                    (and (in p (prod2 (gdom) (gran)))
                         (equal (cdr p) (gfn (car p))))))))

(defthmz grel-funp
  (implies (gprop) (funp (grel)))
  :hints (("Goal" :in-theory (enable funp relation-p)))
  :props (zfc prod2$prop))

(defthmz grel-in-cons
  (implies (and (gprop) (in x (gdom)))
           (in (cons x (gfn x)) (grel)))
  :props (zfc prod2$prop))

(defthmz grel-domain-1
  (implies (gprop) (subset (domain (grel)) (gdom)))
  :hints (("Goal" :in-theory (e/d (subset in-domain-rewrite) (in-cons-apply equal-apply))))
  :props (zfc prod2$prop domain$prop))

(defthmz grel-domain-2
  (implies (gprop) (subset (gdom) (domain (grel))))
  :hints (("Goal" :in-theory (e/d (subset) ())
           :use ((:instance in-car-domain-alt (r (grel)) (x (subset-witness (gdom) (domain (grel))))
                            (p (cons (subset-witness (gdom) (domain (grel)))
                                     (gfn (subset-witness (gdom) (domain (grel))))))))))
  :props (zfc prod2$prop domain$prop))

(defthmz grel-domain
  (implies (gprop) (equal (domain (grel)) (gdom)))
  :hints (("Goal" :use (grel-domain-1 grel-domain-2)
                  :in-theory (e/d (extensionality) (grel-domain-1 grel-domain-2))))
  :props (zfc prod2$prop domain$prop))

(defthmz grel-apply
  (implies (and (gprop) (in x (gdom)))
           (equal (apply (grel) x) (gfn x)))
  :hints (("Goal" :in-theory (enable apply-intro)
           :use (grel-in-cons grel-funp)))
  :props (zfc prod2$prop domain$prop))

(defthmz grel-image
  (implies (gprop) (subset (image (grel)) (gran)))
  :hints (("Goal" :in-theory (enable subset in-image-rewrite)))
  :props (zfc prod2$prop domain$prop inverse$prop))


(encapsulate
  (((fs) => *) ((fadd) => *) ((fmul) => *) ((fzero) => *) ((fone) => *)
   ((fneg) => *) ((frecip) => *) ((fhyp) => *))
  (local (defun fs () 0))
  (local (defun fadd () 0))
  (local (defun fmul () 0))
  (local (defun fzero () 0))
  (local (defun fone () 0))
  (local (defun fneg () 0))
  (local (defun frecip () 0))
  (local (defun fhyp () nil))
  (defthm fhyp-fieldp
    (implies (fhyp) (fieldp (fs) (fadd) (fmul) (fzero) (fone) (fneg) (frecip)))
    :rule-classes nil))

(defmacro f+ (x y) `(apply2 (fadd) ,x ,y))
(defmacro f* (x y) `(apply2 (fmul) ,x ,y))
(defmacro f- (x) `(apply (fneg) ,x))
(defmacro f/ (x) `(apply (frecip) ,x))
(defmacro fN () '(nonzeros (fs) (fzero)))
(defmacro fM () '(restrict (fmul) (prod2 (nonzeros (fs) (fzero)) (nonzeros (fs) (fzero)))))


(defmacro deff (name form &rest args)
  `(defthmz ,name ,form :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop) ,@args))

(defthm f-funps
  (implies (fhyp) (and (funp (fadd)) (funp (fmul)) (funp (fneg)) (funp (frecip))))
  :hints (("Goal" :use fhyp-fieldp :in-theory (disable abelian-group-p abelian-p distributive-p))))

(deff f-add-group
  (implies (fhyp) (abelian-group-p (fs) (fadd) (fzero) (fneg)))
  :hints (("Goal" :use fhyp-fieldp :in-theory (disable abelian-group-p))))

(deff f-mul-group
  (implies (fhyp) (abelian-group-p (fN) (fM) (fone) (frecip)))
  :hints (("Goal" :use fhyp-fieldp :in-theory (disable abelian-group-p))))

(deff f-mul-facts
  (implies (fhyp) (and (equal (domain (fmul)) (prod2 (fs) (fs)))
                       (subset (image (fmul)) (fs))
                       (abelian-p (fs) (fmul))
                       (distributive-p (fs) (fadd) (fmul))
                       (not (equal (fzero) (fone)))))
  :hints (("Goal" :use fhyp-fieldp :in-theory (disable abelian-p distributive-p))))

(in-theory (disable abelian-group-p groupp abelian-p distributive-p group-identity-p
                    group-associative-p group-inverse-p))

(deff f-add-facts
  (implies (fhyp) (and (equal (domain (fadd)) (prod2 (fs) (fs)))
                       (subset (image (fadd)) (fs))
                       (in (fzero) (fs))
                       (group-identity-p (fs) (fadd) (fzero))
                       (group-associative-p (fs) (fadd))
                       (equal (domain (fneg)) (fs))
                       (group-inverse-p (fs) (fadd) (fzero) (fneg))
                       (abelian-p (fs) (fadd))))
  :hints (("Goal" :use f-add-group :in-theory (e/d (abelian-group-p groupp) (f-add-group)))))

(deff f-mul-group-facts
  (implies (fhyp) (and (equal (domain (fM)) (prod2 (fN) (fN)))
                       (subset (image (fM)) (fN))
                       (in (fone) (fN))
                       (group-identity-p (fN) (fM) (fone))
                       (group-associative-p (fN) (fM))
                       (equal (domain (frecip)) (fN))
                       (group-inverse-p (fN) (fM) (fone) (frecip))
                       (abelian-p (fN) (fM))))
  :hints (("Goal" :use f-mul-group :in-theory (e/d (abelian-group-p groupp) (f-mul-group)))))

(in-theory (disable f-add-group f-mul-group))

;;; closure

(deff f-closure-lemma
  (implies (and (subset (image f) s) (equal (domain f) (prod2 s s)) (in x s) (in y s))
           (in (apply2 f x y) s))
  :hints (("Goal" :in-theory (enable apply2)
                  :use ((:instance in-apply-image (r f) (x (cons x y)))
                        (:instance subset-necc (x (image f)) (y s) (a (apply f (cons x y)))))))
  :rule-classes nil)

(deff f-add-closed
  (implies (and (fhyp) (in x (fs)) (in y (fs))) (in (f+ x y) (fs)))
  :hints (("Goal" :use ((:instance f-closure-lemma (f (fadd)) (s (fs)))))))

(deff f-mul-closed
  (implies (and (fhyp) (in x (fs)) (in y (fs))) (in (f* x y) (fs)))
  :hints (("Goal" :use ((:instance f-closure-lemma (f (fmul)) (s (fs)))))))

(deff f-neg-closed
  (implies (and (fhyp) (in x (fs))) (in (f- x) (fs)))
  :hints (("Goal" :use ((:instance group-inverse-p-necc (s (fs)) (op (fadd)) (e (fzero)) (inv (fneg)))))))

(deff f-zero-in (implies (fhyp) (in (fzero) (fs))))

(deff f-one-in-n (implies (fhyp) (in (fone) (fN))))

(deff f-one-in (implies (fhyp) (in (fone) (fs)))
  :hints (("Goal" :use f-one-in-n :in-theory (disable f-one-in-n f-mul-group-facts))))

(deff f-one-not-zero (implies (fhyp) (not (equal (fone) (fzero)))))

(deff f-recip-in-n
  (implies (and (fhyp) (in x (fN))) (in (f/ x) (fN)))
  :hints (("Goal" :use ((:instance group-inverse-p-necc (s (fN)) (op (fM)) (e (fone)) (inv (frecip)))))))

(deff f-recip-closed
  (implies (and (fhyp) (in x (fs)) (not (equal x (fzero)))) (in (f/ x) (fs)))
  :hints (("Goal" :use f-recip-in-n :in-theory (disable f-recip-in-n f-mul-group-facts))))

(deff f-recip-nonzero
  (implies (and (fhyp) (in x (fs)) (not (equal x (fzero)))) (not (equal (f/ x) (fzero))))
  :hints (("Goal" :use f-recip-in-n :in-theory (disable f-recip-in-n f-mul-group-facts))))

;;; additive group

(deff f-add-0-x
  (implies (and (fhyp) (in x (fs))) (equal (f+ (fzero) x) x))
  :hints (("Goal" :use ((:instance group-identity-p-necc (s (fs)) (op (fadd)) (e (fzero)))))))

(deff f-add-x-0
  (implies (and (fhyp) (in x (fs))) (equal (f+ x (fzero)) x))
  :hints (("Goal" :use ((:instance group-identity-p-necc (s (fs)) (op (fadd)) (e (fzero)))))))

(deff f-add-assoc
  (implies (and (fhyp) (in x (fs)) (in y (fs)) (in z (fs)))
           (equal (f+ (f+ x y) z) (f+ x (f+ y z))))
  :hints (("Goal" :use ((:instance group-associative-p-necc (s (fs)) (op (fadd)))))))

(deff f-add-comm
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (f+ x y) (f+ y x)))
  :hints (("Goal" :use ((:instance abelian-p-necc (s (fs)) (op (fadd)))))))

(deff f-add-inv
  (implies (and (fhyp) (in x (fs)))
           (and (equal (f+ x (f- x)) (fzero))
                (equal (f+ (f- x) x) (fzero))))
  :hints (("Goal" :use ((:instance group-inverse-p-necc (s (fs)) (op (fadd)) (e (fzero)) (inv (fneg)))))))

;;; multiplicative facts

(deff f-mul-comm
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (f* x y) (f* y x)))
  :hints (("Goal" :use ((:instance abelian-p-necc (s (fs)) (op (fmul)))))))

(deff f-distrib
  (implies (and (fhyp) (in x (fs)) (in y (fs)) (in z (fs)))
           (equal (f* x (f+ y z)) (f+ (f* x y) (f* x z))))
  :hints (("Goal" :use ((:instance distributive-p-necc (s (fs)) (add (fadd)) (mul (fmul)))))))

(deff f-subset-n-domain
  (implies (fhyp) (subset (prod2 (fN) (fN)) (domain (fmul)))))

(deff f-m-is-mul
  (implies (and (fhyp) (in x (fN)) (in y (fN)))
           (equal (apply2 (fM) x y) (f* x y)))
  :hints (("Goal" :in-theory (disable in-nonzeros))))

(deff f-mul-nz-closed
  (implies (and (fhyp) (in x (fN)) (in y (fN))) (in (f* x y) (fN)))
  :hints (("Goal" :use ((:instance f-closure-lemma (f (fM)) (s (fN))))
                  :in-theory (disable in-nonzeros))))

(deff f-mul-nz-identity
  (implies (and (fhyp) (in x (fN)))
           (and (equal (f* (fone) x) x) (equal (f* x (fone)) x)))
  :hints (("Goal" :use ((:instance group-identity-p-necc (s (fN)) (op (fM)) (e (fone))))
                  :in-theory (disable in-nonzeros))))

(deff f-mul-nz-assoc
  (implies (and (fhyp) (in x (fN)) (in y (fN)) (in z (fN)))
           (equal (f* (f* x y) z) (f* x (f* y z))))
  :hints (("Goal" :use ((:instance group-associative-p-necc (s (fN)) (op (fM))))
                  :in-theory (disable in-nonzeros))))

(deff f-mul-nz-inverse
  (implies (and (fhyp) (in x (fN)))
           (and (equal (f* x (f/ x)) (fone)) (equal (f* (f/ x) x) (fone))))
  :hints (("Goal" :use ((:instance group-inverse-p-necc (s (fN)) (op (fM)) (e (fone)) (inv (frecip))))
                  :in-theory (disable in-nonzeros))))

(in-theory (disable equal-apply))

(deff f-cancel-idem
  (implies (and (fhyp) (in a (fs)) (equal (f+ a a) a))
           (equal a (fzero)))
  :hints (("Goal" :use ((:instance f-add-assoc (x a) (y a) (z (f- a))))))
  :rule-classes nil)

(deff f-mul-x-0
  (implies (and (fhyp) (in x (fs))) (equal (f* x (fzero)) (fzero)))
  :hints (("Goal" :use ((:instance f-cancel-idem (a (f* x (fzero))))
                        (:instance f-distrib (y (fzero)) (z (fzero)))))))

(deff f-mul-0-x
  (implies (and (fhyp) (in x (fs))) (equal (f* (fzero) x) (fzero)))
  :hints (("Goal" :use ((:instance f-mul-comm (x x) (y (fzero)))))))

(deff f-mul-1-x
  (implies (and (fhyp) (in x (fs))) (equal (f* (fone) x) x))
  :hints (("Goal" :cases ((equal x (fzero))))))

(deff f-mul-x-1
  (implies (and (fhyp) (in x (fs))) (equal (f* x (fone)) x))
  :hints (("Goal" :cases ((equal x (fzero))))))

(deff f-mul-nonzero
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (equal (f* x y) (fzero))
                  (or (equal x (fzero)) (equal y (fzero)))))
  :hints (("Goal" :use f-mul-nz-closed :in-theory (disable f-mul-nz-closed))))

(deff f-mul-assoc
  (implies (and (fhyp) (in x (fs)) (in y (fs)) (in z (fs)))
           (equal (f* (f* x y) z) (f* x (f* y z))))
  :hints (("Goal" :cases ((equal x (fzero)) (equal y (fzero)) (equal z (fzero))))))

(deff f-add-comm2
  (implies (and (fhyp) (in x (fs)) (in y (fs)) (in z (fs)))
           (equal (f+ x (f+ y z)) (f+ y (f+ x z))))
  :hints (("Goal" :use ((:instance f-add-assoc (x x) (y y) (z z))
                        (:instance f-add-assoc (x y) (y x) (z z))
                        (:instance f-add-comm (x x) (y y)))
                  :in-theory (disable f-add-assoc f-add-comm))))

(deff f-mul-comm2
  (implies (and (fhyp) (in x (fs)) (in y (fs)) (in z (fs)))
           (equal (f* x (f* y z)) (f* y (f* x z))))
  :hints (("Goal" :use ((:instance f-mul-assoc (x x) (y y) (z z))
                        (:instance f-mul-assoc (x y) (y x) (z z))
                        (:instance f-mul-comm (x x) (y y)))
                  :in-theory (disable f-mul-assoc f-mul-comm))))

(deff f-neg-unique
  (implies (and (fhyp) (in a (fs)) (in b (fs)) (equal (f+ a b) (fzero)))
           (equal (f- a) b))
  :hints (("Goal" :use ((:instance f-add-assoc (x (f- a)) (y a) (z b)))
                  :in-theory (disable f-add-assoc)))
  :rule-classes nil)

(deff f-add-cancel-1
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (and (equal (f+ x (f+ (f- x) y)) y)
                (equal (f+ (f- x) (f+ x y)) y)))
  :hints (("Goal" :use ((:instance f-add-assoc (x x) (y (f- x)) (z y))
                        (:instance f-add-assoc (x (f- x)) (y x) (z y)))
                  :in-theory (disable f-add-assoc))))

(deff f-neg-neg
  (implies (and (fhyp) (in x (fs))) (equal (f- (f- x)) x))
  :hints (("Goal" :use ((:instance f-neg-unique (a (f- x)) (b x))))))

(deff f-neg-0
  (implies (fhyp) (equal (f- (fzero)) (fzero)))
  :hints (("Goal" :use ((:instance f-neg-unique (a (fzero)) (b (fzero)))))))

(deff f-neg-add
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (f- (f+ x y)) (f+ (f- x) (f- y))))
  :hints (("Goal" :use ((:instance f-neg-unique (a (f+ x y)) (b (f+ (f- x) (f- y)))))
                  :in-theory (disable f-add-comm))))

(deff f-mul-neg-right
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (f* x (f- y)) (f- (f* x y))))
  :hints (("Goal" :use ((:instance f-neg-unique (a (f* x y)) (b (f* x (f- y))))
                        (:instance f-distrib (x x) (y y) (z (f- y))))
                  :in-theory (disable f-distrib))))

(deff f-mul-neg-left
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (f* (f- x) y) (f- (f* x y))))
  :hints (("Goal" :use ((:instance f-mul-comm (x (f- x)) (y y))
                        (:instance f-mul-comm (x x) (y y)))
                  :in-theory (disable f-mul-comm))))

(deff f-distrib-right
  (implies (and (fhyp) (in x (fs)) (in y (fs)) (in z (fs)))
           (equal (f* (f+ y z) x) (f+ (f* y x) (f* z x))))
  :hints (("Goal" :use ((:instance f-mul-comm (x x) (y (f+ y z)))
                        (:instance f-mul-comm (x x) (y y))
                        (:instance f-mul-comm (x x) (y z)))
                  :in-theory (disable f-mul-comm))))

(deff f-recip-cancel
  (implies (and (fhyp) (in x (fs)) (not (equal x (fzero))) (in y (fs)))
           (and (equal (f* x (f* (f/ x) y)) y)
                (equal (f* (f/ x) (f* x y)) y)))
  :hints (("Goal" :use ((:instance f-mul-assoc (x x) (y (f/ x)) (z y))
                        (:instance f-mul-assoc (x (f/ x)) (y x) (z y)))
                  :in-theory (disable f-mul-assoc))))

(deff f-neg-mul-cancel
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (f+ x (f- x)) (fzero))))


(encapsulate
  (((fhyp2) => *))
  (local (defun fhyp2 () nil))
  (defthm fhyp2-minus-one
    (implies (fhyp2) (minus-one-not-square (fs) (fmul) (fneg) (fone)))
    :rule-classes nil))

(defmacro fS2 () '(prod2 (fs) (fs)))

(defmacro def-crel (name hyps dom ran rel fn)
  (let ((fi `((gprop (lambda () (and ,@hyps (zfc) (prod2$prop) (domain$prop) (inverse$prop) (diff$prop) (restrict$prop))))
              (gdom (lambda () ,dom))
              (gran (lambda () ,ran))
              (grel (lambda () ,rel))
              (gfn ,fn))))
    `(progn
       (deff ,(prefix-symbol (symbol-name name) '-funp)
         (implies (and ,@hyps) (funp ,rel))
         :hints (("Goal" :use ((:functional-instance grel-funp ,@fi)))))
       (deff ,(prefix-symbol (symbol-name name) '-domain)
         (implies (and ,@hyps) (equal (domain ,rel) ,dom))
         :hints (("Goal" :use ((:functional-instance grel-domain ,@fi)))))
       (deff ,(prefix-symbol (symbol-name name) '-image)
         (implies (and ,@hyps) (subset (image ,rel) ,ran))
         :hints (("Goal" :use ((:functional-instance grel-image ,@fi)))))
       (deff ,(prefix-symbol (symbol-name name) '-apply)
         (implies (and ,@hyps (in x ,dom))
                  (equal (apply ,rel x) ,(list fn 'x)))
         :hints (("Goal" :use ((:functional-instance grel-apply ,@fi))))))))

(def-crel c-neg ((c-neg$prop) (fhyp)) (fS2) (fS2) (c-neg (fs) (fneg))
  (lambda (x) (cons (apply (fneg) (car x)) (apply (fneg) (cdr x)))))

(def-crel c-add ((c-add$prop) (fhyp)) (prod2 (fS2) (fS2)) (fS2) (c-add (fs) (fadd))
  (lambda (x) (cons (apply2 (fadd) (car (car x)) (car (cdr x)))
                    (apply2 (fadd) (cdr (car x)) (cdr (cdr x))))))

(def-crel c-mul ((c-mul$prop) (fhyp)) (prod2 (fS2) (fS2)) (fS2) (c-mul (fs) (fadd) (fmul) (fneg))
  (lambda (x) (cons (apply2 (fadd) (apply2 (fmul) (car (car x)) (car (cdr x)))
                            (apply (fneg) (apply2 (fmul) (cdr (car x)) (cdr (cdr x)))))
                    (apply2 (fadd) (apply2 (fmul) (car (car x)) (cdr (cdr x)))
                            (apply2 (fmul) (cdr (car x)) (car (cdr x)))))))

(deff f-norm-lemma
  (implies (and (fhyp) (in a (fs)) (in b (fs)) (not (equal b (fzero))))
           (equal (f+ (f* (f* a (f/ b)) (f* a (f/ b))) (fone))
                  (f* (f+ (f* a a) (f* b b)) (f* (f/ b) (f/ b)))))
  :rule-classes nil)

(deff f-add-eq-zero
  (implies (and (fhyp) (in x (fs)) (in y (fs)))
           (equal (equal (f+ x y) (fzero)) (equal x (f- y))))
  :hints (("Goal" :use ((:instance f-neg-unique (a y) (b x))))))

(deff f-norm-nonzero
  (implies (and (fhyp) (fhyp2) (in a (fs)) (in b (fs))
                (not (and (equal a (fzero)) (equal b (fzero)))))
           (not (equal (f+ (f* a a) (f* b b)) (fzero))))
  :hints (("Goal" :cases ((equal b (fzero))))
          ("Subgoal 2" :use (f-norm-lemma fhyp2-minus-one
                             (:instance f-neg-unique (a (fone)) (b (f* (f* a (f/ b)) (f* a (f/ b)))))
                             (:instance minus-one-not-square-necc (s (fs)) (mul (fmul)) (neg (fneg))
                                        (one (fone)) (x (f* a (f/ b)))))
                       :in-theory (disable f-add-eq-zero))))

(defthm equal-consp-cons
  (implies (consp x)
           (equal (equal x (cons a b))
                  (and (equal (car x) a) (equal (cdr x) b)))))

(def-crel c-recip ((c-recip$prop) (fhyp) (fhyp2))
  (diff (fS2) (singleton (cons (fzero) (fzero)))) (fS2)
  (c-recip (fs) (fadd) (fmul) (fzero) (fneg) (frecip))
  (lambda (x) (cons (apply2 (fmul) (car x) (apply (frecip) (c-norm2 x (fadd) (fmul))))
                    (apply2 (fmul) (apply (fneg) (cdr x)) (apply (frecip) (c-norm2 x (fadd) (fmul)))))))

(defmacro cadd () '(c-add (fs) (fadd)))
(defmacro cmul () '(c-mul (fs) (fadd) (fmul) (fneg)))
(defmacro cneg () '(c-neg (fs) (fneg)))
(defmacro crecip () '(c-recip (fs) (fadd) (fmul) (fzero) (fneg) (frecip)))

(deff c-add-apply2
  (implies (and (c-add$prop) (fhyp) (in u (fS2)) (in v (fS2)))
           (equal (apply2 (cadd) u v)
                  (cons (f+ (car u) (car v)) (f+ (cdr u) (cdr v)))))
  :hints (("Goal" :expand ((apply2 (cadd) u v)))))

(deff c-mul-apply2
  (implies (and (c-mul$prop) (fhyp) (in u (fS2)) (in v (fS2)))
           (equal (apply2 (cmul) u v)
                  (cons (f+ (f* (car u) (car v)) (f- (f* (cdr u) (cdr v))))
                        (f+ (f* (car u) (cdr v)) (f* (cdr u) (car v))))))
  :hints (("Goal" :expand ((apply2 (cmul) u v)))))

(deff c-i-squared
  (implies (and (c-mul$prop) (c-neg$prop) (fhyp))
           (equal (apply2 (cmul) (cons (fzero) (fone)) (cons (fzero) (fone)))
                  (apply (cneg) (cons (fone) (fzero))))))


(defmacro c0 () '(cons (fzero) (fzero)))
(defmacro c1 () '(cons (fone) (fzero)))

(deff c-neg-apply-better
  (implies (and (c-neg$prop) (fhyp) (in x (fS2)))
           (equal (apply (cneg) x)
                  (cons (f- (car x)) (f- (cdr x)))))
  :hints (("Goal" :use c-neg-apply :in-theory (disable c-neg-apply in-prod2))))

(deff c-add-group
  (implies (and (c-add$prop) (c-neg$prop) (fhyp))
           (abelian-group-p (fS2) (cadd) (c0) (cneg)))
  :hints (("Goal" :in-theory (enable abelian-group-p groupp group-identity-p group-associative-p
                                     group-inverse-p abelian-p))))

(deff c-mul-abelian
  (implies (and (c-mul$prop) (fhyp))
           (abelian-p (fS2) (cmul)))
  :hints (("Goal" :in-theory (enable abelian-p))))

(deff c-mul-assoc
  (implies (and (c-mul$prop) (fhyp))
           (group-associative-p (fS2) (cmul)))
  :hints (("Goal" :in-theory (enable group-associative-p))))

(deff c-distributive
  (implies (and (c-mul$prop) (c-add$prop) (fhyp))
           (distributive-p (fS2) (cadd) (cmul)))
  :hints (("Goal" :in-theory (enable distributive-p))))


(defmacro cN2 () '(nonzeros (fS2) (c0)))
(defmacro cM2 () '(restrict (cmul) (prod2 (cN2) (cN2))))

(deff image-elim
  (implies (and (funp f) (equal (domain f) (prod2 a b)) (in w (image f)))
           (and (in (car (apply (inverse f) w)) a)
                (in (cdr (apply (inverse f) w)) b)
                (equal (apply2 f (car (apply (inverse f) w)) (cdr (apply (inverse f) w))) w)))
  :hints (("Goal" :use ((:instance in-image-implies-in-apply-inverse-domain (y w) (r f) (d (domain f)))
                        (:instance apply-apply-inverse (x w)))
                  :in-theory (e/d (apply2) (in-image-implies-in-apply-inverse-domain apply-apply-inverse))))
  :rule-classes nil)

(deff c-subset-n2-domain
  (implies (and (c-mul$prop) (fhyp))
           (subset (prod2 (cN2) (cN2)) (domain (cmul)))))

(deff c-m2-is-cmul
  (implies (and (c-mul$prop) (fhyp) (in x (cN2)) (in y (cN2)))
           (equal (apply2 (cM2) x y) (apply2 (cmul) x y)))
  :hints (("Goal" :in-theory (disable in-nonzeros c-mul-apply2 in-prod2))))

(deff c-m2-domain
  (implies (and (c-mul$prop) (fhyp))
           (equal (domain (cM2)) (prod2 (cN2) (cN2))))
  :hints (("Goal" :in-theory (disable in-nonzeros))))

(deff c-m2-funp
  (implies (and (c-mul$prop) (fhyp)) (funp (cM2))))

(deff c-recip-domain-n
  (implies (and (c-recip$prop) (fhyp) (fhyp2))
           (equal (domain (crecip)) (cN2)))
  :hints (("Goal" :in-theory (enable nonzeros))))

(deff c-recip-apply-better
  (implies (and (c-recip$prop) (fhyp) (fhyp2) (in x (fS2)) (not (equal x (c0))))
           (equal (apply (crecip) x)
                  (cons (f* (car x) (f/ (f+ (f* (car x) (car x)) (f* (cdr x) (cdr x)))))
                        (f* (f- (cdr x)) (f/ (f+ (f* (car x) (car x)) (f* (cdr x) (cdr x))))))))
  :hints (("Goal" :use c-recip-apply :in-theory (disable c-recip-apply in-prod2 equal-consp-cons))))

(deff c-recip-in-s2
  (implies (and (c-recip$prop) (fhyp) (fhyp2) (in x (fS2)) (not (equal x (c0))))
           (in (apply (crecip) x) (fS2)))
  :hints (("Goal" :in-theory (disable c-recip-apply))))

(deff c-mul-recip
  (implies (and (c-recip$prop) (c-mul$prop) (fhyp) (fhyp2) (in x (fS2)) (not (equal x (c0))))
           (and (equal (apply2 (cmul) x (apply (crecip) x)) (c1))
                (equal (apply2 (cmul) (apply (crecip) x) x) (c1))))
  :hints (("Goal" :use ((:instance f-mul-nz-inverse
                                   (x (f+ (f* (car x) (car x)) (f* (cdr x) (cdr x)))))
                        (:instance f-norm-nonzero (a (car x)) (b (cdr x))))
                  :in-theory (disable f-mul-nz-inverse))))


(deff c-mul-1
  (implies (and (c-mul$prop) (fhyp) (in x (fS2)))
           (and (equal (apply2 (cmul) (c1) x) x)
                (equal (apply2 (cmul) x (c1)) x))))

(deff c-mul-0
  (implies (and (c-mul$prop) (fhyp) (in x (fS2)))
           (equal (apply2 (cmul) x (c0)) (c0))))

(deff c-mul-closed
  (implies (and (c-mul$prop) (fhyp) (in x (fS2)) (in y (fS2)))
           (in (apply2 (cmul) x y) (fS2))))

(deff c-mul-assoc-apply
  (implies (and (c-mul$prop) (fhyp) (in x (fS2)) (in y (fS2)) (in z (fS2)))
           (equal (apply2 (cmul) (apply2 (cmul) x y) z)
                  (apply2 (cmul) x (apply2 (cmul) y z))))
  :hints (("Goal" :use (c-mul-assoc
                        (:instance group-associative-p-necc (s (fS2)) (op (cmul))))
                  :in-theory (disable c-mul-assoc c-mul-apply2 in-prod2)))
  :rule-classes nil)

(deff c-no-zero-div
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2)
                (in x (fS2)) (not (equal x (c0))) (in y (fS2))
                (equal (apply2 (cmul) x y) (c0)))
           (equal y (c0)))
  :hints (("Goal" :use ((:instance c-mul-assoc-apply (x (apply (crecip) x)) (y x) (z y)))
                  :in-theory (disable c-mul-apply2 in-prod2 c-recip-apply-better c-recip-apply
                                      equal-consp-cons)))
  :rule-classes nil)

(deff c-recip-nonzero
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2)
                (in x (fS2)) (not (equal x (c0))))
           (not (equal (apply (crecip) x) (c0))))
  :hints (("Goal" :use ((:instance c-mul-recip))
                  :in-theory (disable c-mul-recip c-mul-apply2 in-prod2 c-recip-apply-better c-recip-apply
                                      equal-consp-cons))))

(deff c-mul-nonzero
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2)
                (in x (fS2)) (not (equal x (c0))) (in y (fS2)) (not (equal y (c0))))
           (not (equal (apply2 (cmul) x y) (c0))))
  :hints (("Goal" :use ((:instance c-no-zero-div))
                  :in-theory (disable c-mul-apply2 in-prod2 c-recip-apply-better c-recip-apply
                                      equal-consp-cons))))

(deff c-m2-image
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2))
           (subset (image (cM2)) (cN2)))
  :hints (("Goal" :in-theory (e/d (subset) (c-mul-apply2 in-prod2 c-recip-apply-better c-recip-apply
                                            equal-consp-cons))
                  :use ((:instance image-elim (f (cM2)) (a (cN2)) (b (cN2))
                                   (w (subset-witness (image (cM2)) (cN2))))))))


(deff c-one-in-n2
  (implies (fhyp) (in (c1) (cN2))))

(deff c-mul-assoc-apply-rw
  (implies (and (c-mul$prop) (fhyp) (in x (fS2)) (in y (fS2)) (in z (fS2)))
           (equal (apply2 (cmul) (apply2 (cmul) x y) z)
                  (apply2 (cmul) x (apply2 (cmul) y z))))
  :hints (("Goal" :use c-mul-assoc-apply)))

(in-theory (disable c-mul-assoc-apply-rw))

(deff c-n2-identity
  (implies (and (c-mul$prop) (fhyp))
           (group-identity-p (cN2) (cM2) (c1)))
  :hints (("Goal" :in-theory (e/d (group-identity-p)
                                  (c-mul-apply2 c-recip-apply-better c-recip-apply)))))

(deff c-n2-assoc
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2))
           (group-associative-p (cN2) (cM2)))
  :hints (("Goal" :in-theory (e/d (group-associative-p c-mul-assoc-apply-rw)
                                  (c-mul-apply2 c-recip-apply-better c-recip-apply)))))

(deff c-recip-in-n2
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2) (in x (cN2)))
           (in (apply (crecip) x) (cN2)))
  :hints (("Goal" :in-theory (disable c-mul-apply2 c-recip-apply-better c-recip-apply in-prod2))))

(deff c-n2-inverse
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2))
           (group-inverse-p (cN2) (cM2) (c1) (crecip)))
  :hints (("Goal" :in-theory (e/d (group-inverse-p)
                                  (c-mul-apply2 c-recip-apply-better c-recip-apply in-prod2)))))

(deff c-n2-abelian
  (implies (and (c-mul$prop) (fhyp))
           (abelian-p (cN2) (cM2)))
  :hints (("Goal" :in-theory (e/d (abelian-p) (c-recip-apply-better c-recip-apply)))))

(deff c-mul-group
  (implies (and (c-mul$prop) (c-recip$prop) (fhyp) (fhyp2))
           (abelian-group-p (cN2) (cM2) (c1) (crecip)))
  :hints (("Goal" :in-theory (e/d (abelian-group-p groupp)
                                  (c-mul-apply2 c-recip-apply-better c-recip-apply)))))

(deff c-field
  (implies (and (c-add$prop) (c-mul$prop) (c-neg$prop) (c-recip$prop) (fhyp) (fhyp2))
           (fieldp (fS2) (cadd) (cmul) (c0) (c1) (cneg) (crecip)))
  :hints (("Goal" :in-theory (disable c-mul-apply2 c-recip-apply-better c-recip-apply))))


(defthmz complex-i-squared
  (implies (fieldp s add mul zero one neg recip)
           (equal (apply2 (c-mul s add mul neg) (cons zero one) (cons zero one))
                  (apply (c-neg s neg) (cons one zero))))
  :hints (("Goal" :use ((:functional-instance c-i-squared
                         (fs (lambda () s)) (fadd (lambda () add)) (fmul (lambda () mul))
                         (fzero (lambda () zero)) (fone (lambda () one)) (fneg (lambda () neg))
                         (frecip (lambda () recip))
                         (fhyp (lambda () (fieldp s add mul zero one neg recip)))))
           :in-theory (disable fieldp))
          (and stable-under-simplificationp '(:in-theory (enable fieldp))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-mul$prop c-neg$prop))


(defthmz complex-construction-is-field
  (implies (and (fieldp s add mul zero one neg recip)
                (minus-one-not-square s mul neg one))
           (fieldp (prod2 s s) (c-add s add) (c-mul s add mul neg)
                   (cons zero zero) (cons one zero) (c-neg s neg)
                   (c-recip s add mul zero neg recip)))
  :hints (("Goal" :use ((:functional-instance c-field
                         (fs (lambda () s)) (fadd (lambda () add)) (fmul (lambda () mul))
                         (fzero (lambda () zero)) (fone (lambda () one)) (fneg (lambda () neg))
                         (frecip (lambda () recip))
                         (fhyp (lambda () (fieldp s add mul zero one neg recip)))
                         (fhyp2 (lambda () (minus-one-not-square s mul neg one)))))
           :in-theory (disable fieldp minus-one-not-square))
          (and stable-under-simplificationp '(:in-theory (enable fieldp minus-one-not-square))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-add$prop c-mul$prop c-neg$prop c-recip$prop))
