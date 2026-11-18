(in-package "ZF")
(ld "t7.lisp")
(defthmz image-pig-g
  (subset (image (pig-g f n)) (+ -1 n))
  :hints (("Goal" :in-theory (enable subset pig-g$comprehension in-prod2)
           :use ((:instance in-image-necc (f (pig-g f n)) (x (subset-witness (image (pig-g f n)) (+ -1 n)))))))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))

(defthmz funp-inverse-pig-g
  (implies (and (natp n) (injective-funp f) (equal (domain f) (+ 1 n)))
           (funp (inverse (pig-g f n))))
  :hints (("Goal" :expand ((funp (inverse (pig-g f n))))
           :in-theory (e/d (in-inverse pig-g$comprehension in-prod2) (injective-funp)))
          ("Subgoal 2''" :use ((:instance pig-h-injective
                               (x (cdr (car (funp-witness (inverse (pig-g f n))))))
                               (y (cdr (mv-nth 1 (funp-witness (inverse (pig-g f n))))))))))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))
