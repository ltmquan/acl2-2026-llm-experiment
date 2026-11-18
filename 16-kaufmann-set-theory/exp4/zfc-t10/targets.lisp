(defthmz metric-topology-is-topology
  (implies (metric-p d x)
           (and (tpp (metric-topology d x))
                (equal (union (metric-topology d x)) x)))
  :props (zfc prod2$prop diff$prop metric-topology$prop))

(defthmz metric-topology-is-hausdorff
  (implies (metric-p d x) (hausdorff (metric-topology d x)))
  :props (dr-sum-prop diff$prop metric-topology$prop))

(defthmz rationals-metric
  (metric-p (q-dist) (rationals))
  :props (dr-sum-prop q-dist$prop))
