(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(defun-sk dr-valued (d x)
  (forall (a b) (implies (and (in a x) (in b x)) (drp (apply d (cons a b))))))

(defun-sk metric-axioms (d x)
  (forall (a b c)
    (implies (and (in a x) (in b x) (in c x))
             (and (subset (r2dr 0) (apply d (cons a b)))
                  (iff (equal (apply d (cons a b)) (r2dr 0)) (equal a b))
                  (equal (apply d (cons a b)) (apply d (cons b a)))
                  (subset (apply d (cons a c))
                          (dr+ (apply d (cons a b)) (apply d (cons b c))))))))

(defun metric-p (d x)
  (and (funp d) (equal (domain d) (prod2 x x)) (dr-valued d x)
       (metric-axioms d x)))

(defun-sk ball-inside (u a eps d x)
  (forall b (implies (and (in b x) (not (in eps (apply d (cons a b)))))
                     (in b u))))

(defun-sk has-ball (u a d x)
  (exists eps (and (rationalp eps) (< 0 eps) (ball-inside u a eps d x))))

(defun-sk metric-open-p (u d x)
  (forall a (implies (in a u) (has-ball u a d x))))

(zsub metric-topology (d x) u (powerset x) (metric-open-p u d x))

(zsub q-dist () p (prod2 (prod2 (rationals) (rationals)) (powerset (rationals)))
      (equal (cdr p) (r2dr (abs (- (car (car p)) (cdr (car p)))))))
