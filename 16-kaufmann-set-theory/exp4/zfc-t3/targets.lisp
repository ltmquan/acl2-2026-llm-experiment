(defthmz principal-filter-is-ultrafilter
  (implies (in a s) (ultrafilter-on (principal-filter a s) s))
  :props (zfc diff$prop principal-filter$prop))

(defthmz ultra-iff-maximal
  (implies (filter-on u s) (iff (ultra-p u s) (maximal-filter-p u s)))
  :props (zfc diff$prop))

(defthmz ultrafilter-prime
  (implies (and (ultrafilter-on u s) (subset x s) (subset y s)
                (in (union2 x y) u))
           (or (in x u) (in y u)))
  :props (zfc diff$prop))

(defthmz ultrafilter-with-finite-member-is-principal
  (implies (and (ultrafilter-on u s) (in x u) (finite x))
           (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))

(defthmz ultrafilter-on-finite-set-is-principal
  (implies (and (ultrafilter-on u s) (finite s))
           (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))
