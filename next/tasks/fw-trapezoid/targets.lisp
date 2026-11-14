(defthm trapezoid-rule-error
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (sum-cubed-deltas p)))))

(defthm trapezoid-rule-error-mesh
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (- (car (last p)) (car p)) (expt (mesh p) 2)))))
