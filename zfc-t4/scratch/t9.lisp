(in-package "ZF")
(ld "t8.lisp")
(defthmz injective-funp-pig-g
  (implies (and (natp n) (injective-funp f) (equal (domain f) (+ 1 n)) (subset (image f) n))
           (injective-funp (pig-g f n)))
  :hints (("Goal" :in-theory (enable injective-funp)))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))

(defun pig-ind (f n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) f (pig-ind (pig-g f n) (1- n))))

(defthmz pigeon-base
  (implies (and (equal (domain f) 1) (subset (image f) 0)) nil)
  :rule-classes nil
  :hints (("Goal" :use ((:instance apply-in-codomain (x 0) (s 0)))
           :in-theory (disable apply-in-codomain)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pigeon-core
  (implies (and (natp n) (injective-funp f) (equal (domain f) (+ 1 n)) (subset (image f) n)) nil)
  :rule-classes nil
  :hints (("Goal" :induct (pig-ind f n) :in-theory (disable injective-funp))
          ("Subgoal *1/1" :use pigeon-base))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))
