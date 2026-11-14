; Arrayset Revisited -- correctness theorems.
;
; The theorems of Figure 8 (aset_add-val-at-used_head--thm,
; aset_del-val-at-free_head--thm) and Figure 9
; (aset_del_head-used-list--thm, aset_del_head-free-list--thm), with the
; paper's names and statements, together with the supporting lemmas.
; ARR_SZ is disabled (including its executable counterpart), so the proofs
; hold for any array size 1 < ARR_SZ < 2^32; build.sh certifies the same
; book for ARR_SZ = 1024 and for ARR_SZ = 6.

(in-package "RTL")
(include-book "arrayset-defs")
(local (include-book "rtl/rel11/lib/bits" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(defthm anext-rangep-lemma
  (implies (and (anext-rangep i n anext)
                (natp i) (natp j) (natp n) (<= i j) (< j n))
           (and (natp (ag j anext))
                (< (ag j anext) n)))
  :rule-classes nil)

(defthm anext-rangep-0-integerp
  (implies (and (anext-rangep 0 n anext)
                (natp j) (natp n) (< j n))
           (integerp (ag j anext)))
  :hints (("Goal" :use (:instance anext-rangep-lemma (i 0)))))

(defthm anext-rangep-0-linear
  (implies (and (anext-rangep 0 n anext)
                (natp j) (natp n) (< j n))
           (and (<= 0 (ag j anext))
                (< (ag j anext) n)))
  :hints (("Goal" :use (:instance anext-rangep-lemma (i 0))))
  :rule-classes :linear)

(in-theory (disable anext-rangep))

(defthm si-bits-si
  (implies (unsigned-byte-p 64 val)
           (equal (bits (si val 64) 63 0) val))
  :hints (("Goal" :in-theory (enable bits-si bvecp))))

(in-theory (disable log< log= log<> logand1 lognot1))

(defthm used_head-rewrite
  (equal (used_head aset)
         (if (< (ag 'used_lst aset) (arr_sz))
             (ag (ag 'used_lst aset) (ag 'anext aset))
           (arr_sz)))
  :hints (("Goal" :in-theory (enable used_head log<))))

(defthm free_head-rewrite
  (equal (free_head aset)
         (if (< (ag 'free_lst aset) (arr_sz))
             (ag (ag 'free_lst aset) (ag 'anext aset))
           (arr_sz)))
  :hints (("Goal" :in-theory (enable free_head log<))))

;;; ------------------------------------------------------------------
;;; aset_add

(defthm aset_add-val-at-used_head--thm
  (implies
   (and (asetp aset)
        (aset-free-to-used-preconditionp aset)
        (unsigned-byte-p 64 val))
   (= (si (ag (used_head (aset_add val aset))
              (ag 'avals (aset_add val aset))) 64)
      (si val 64)))
  :hints (("Goal" :in-theory (enable asetp aset-free-to-used-preconditionp
                                     aset-common-preconditionp
                                     aset_add aset_transfer used_head
                                     log< log= false$ true$))))

;;; ------------------------------------------------------------------
;;; aset_find_val_from

(defun find-okp (r val aset)
  (or (equal r (arr_sz))
      (and (natp r)
           (< r (arr_sz))
           (equal (si (ag (ag r (ag 'anext aset)) (ag 'avals aset)) 64)
                  (si val 64)))))

(defthm aset_find_val_from-loop-0-okp
  (implies (and (find-okp retval val aset)
                (or (not (equal done 0))
                    (and (natp idx) (< idx (arr_sz))))
                (anext-rangep 0 (arr_sz) (ag 'anext aset)))
           (find-okp (mv-nth 1 (aset_find_val_from-loop-0
                                i aset val start idx retval done))
                     val aset))
  :hints (("Goal" :in-theory (enable aset_find_val_from-loop-0 log= true$))))

(defthm aset_find_val_from-okp
  (implies (and (anext-rangep 0 (arr_sz) (ag 'anext aset))
                (natp start))
           (find-okp (aset_find_val_from start val aset) val aset))
  :hints (("Goal" :in-theory (e/d (aset_find_val_from log< lognot1)
                                  (aset_find_val_from-loop-0-okp))
           :use (:instance aset_find_val_from-loop-0-okp
                           (i 0) (idx start) (retval (arr_sz))
                           (done (lognot1 (log< start (arr_sz))))))))

(defthm aset_find_val_from-found
  (implies (and (anext-rangep 0 (arr_sz) (ag 'anext aset))
                (natp start)
                (< (aset_find_val_from start val aset) (arr_sz)))
           (and (natp (aset_find_val_from start val aset))
                (equal (si (ag (ag (aset_find_val_from start val aset)
                                   (ag 'anext aset))
                               (ag 'avals aset))
                           64)
                       (si val 64))))
  :hints (("Goal" :use aset_find_val_from-okp
           :in-theory (e/d (find-okp) (aset_find_val_from-okp)))))

(in-theory (disable find-okp))

;;; ------------------------------------------------------------------
;;; aset_del

(defthm aset_del-val-at-free_head--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (unsigned-byte-p 64 val)
        (< (aset_find_val_from (ag 'used_lst aset) val aset) (ARR_SZ)))
   (= (si (ag (free_head (aset_del val aset))
              (ag 'avals (aset_del val aset))) 64)
      (si val 64)))
  :hints (("Goal" :in-theory (e/d (asetp aset-used-to-free-preconditionp
                                     aset-common-preconditionp
                                     aset_del aset_del_head aset_transfer free_head
                                     log< log= log<> logand1 false$ true$)
                                  (aset_find_val_from-found))
           :use (:instance aset_find_val_from-found
                           (start (ag 'used_lst aset))))))

;;; ------------------------------------------------------------------
;;; Walking the anext links.

(defthm aset-walk-frame
  (implies (or (not (member-equal x (aset-walk idx tail fuel anext)))
               (equal x tail))
           (equal (aset-walk idx tail fuel (as x v anext))
                  (aset-walk idx tail fuel anext))))

(defthm aset-walk-closedp-frame
  (implies (or (not (member-equal x (aset-walk idx tail fuel anext)))
               (equal x tail))
           (equal (aset-walk-closedp idx tail fuel (as x v anext))
                  (aset-walk-closedp idx tail fuel anext))))

(defthm aset-walk-more-fuel
  (implies (and (aset-walk-closedp idx tail k anext)
                (natp k2) (<= k k2))
           (and (aset-walk-closedp idx tail k2 anext)
                (equal (aset-walk idx tail k2 anext)
                       (aset-walk idx tail k anext))))
  :rule-classes nil)

(defthm aset-walk-closedp-len
  (implies (aset-walk-closedp idx tail k anext)
           (aset-walk-closedp idx tail (len (aset-walk idx tail k anext))
                              anext)))

(defthm len-aset-walk
  (<= (len (aset-walk idx tail k anext)) (nfix k))
  :rule-classes :linear)

(defthm member-tail-aset-walk
  (implies (aset-walk-closedp idx tail k anext)
           (member-equal tail (aset-walk idx tail k anext))))

(defthm consp-aset-walk
  (equal (consp (aset-walk idx tail k anext))
         (not (zp k))))

(defthm car-aset-walk
  (implies (not (zp k))
           (equal (car (aset-walk idx tail k anext)) idx)))

(defthm member-idx-aset-walk
  (implies (not (zp k))
           (member-equal idx (aset-walk idx tail k anext))))

(defthm member-equal-append
  (iff (member-equal a (append x y))
       (or (member-equal a x) (member-equal a y))))

(defthm member-append-no-dups
  (implies (and (no-duplicatesp-equal (append x y))
                (member-equal a y))
           (not (member-equal a x))))

(defthm member-append-no-dups-2
  (implies (and (no-duplicatesp-equal (append x y))
                (member-equal a x))
           (not (member-equal a y))))

(defthm no-duplicatesp-append-left
  (implies (no-duplicatesp-equal (append x y))
           (no-duplicatesp-equal x)))

(defthm aset-walk-open
  (implies (and (not (zp k)) (not (equal idx tail)))
           (equal (aset-walk idx tail k anext)
                  (cons idx (aset-walk (ag idx anext) tail (1- k) anext)))))

(defthm aset-walk-closedp-open
  (implies (and (not (zp k)) (not (equal idx tail)))
           (equal (aset-walk-closedp idx tail k anext)
                  (aset-walk-closedp (ag idx anext) tail (1- k) anext))))

(defthm aset-walk-at-tail
  (implies (not (zp k))
           (equal (aset-walk tail tail k anext) (list tail))))

(defthm aset-walk-closedp-at-tail
  (implies (not (zp k))
           (aset-walk-closedp tail tail k anext)))

(defthm aset-walk-zp
  (implies (zp k) (equal (aset-walk idx tail k anext) nil)))

(defthm aset-walk-closedp-zp
  (implies (zp k) (not (aset-walk-closedp idx tail k anext))))

(in-theory (disable aset-walk aset-walk-closedp))

;; Walks that close within k steps close within any j >= their length.
(defthm aset-walk-less-fuel
  (implies (and (aset-walk-closedp idx tail k anext)
                (natp k)
                (natp j)
                (<= (len (aset-walk idx tail k anext)) j))
           (and (aset-walk-closedp idx tail j anext)
                (equal (aset-walk idx tail j anext)
                       (aset-walk idx tail k anext))))
  :hints (("Goal" :use ((:instance aset-walk-more-fuel
                                   (k (len (aset-walk idx tail k anext)))
                                   (k2 j))
                        (:instance aset-walk-more-fuel
                                   (k (len (aset-walk idx tail k anext)))
                                   (k2 k)))))
  :rule-classes nil)

;; The used list after unlinking its head h (h /= s, where s is the tail
;; and h = anext[s]): walking from anext[h] in the updated array gives the
;; cdr of the old list.
(defthm used-walk-after-unlink-1
  (implies (and (not (zp k))
                (aset-walk-closedp h s k a)
                (not (equal h s))
                (no-duplicatesp-equal (aset-walk h s k a))
                (not (member-equal f (aset-walk h s k a))))
           (equal (aset-walk (ag h a) s k
                             (as f h (as h v (as s (ag h a) a))))
                  (cdr (aset-walk h s k a))))
  :hints (("Goal" :use ((:instance aset-walk-more-fuel
                                   (idx (ag h a)) (tail s)
                                   (anext a) (k (1- k)) (k2 k))))))

(defthm used-walk-after-unlink-2
  (implies (and (not (zp k))
                (aset-walk-closedp h s k a)
                (not (equal h s))
                (no-duplicatesp-equal (aset-walk h s k a)))
           (equal (aset-walk (ag h a) s k
                             (as h v (as s (ag h a) a)))
                  (cdr (aset-walk h s k a))))
  :hints (("Goal" :use ((:instance aset-walk-more-fuel
                                   (idx (ag h a)) (tail s)
                                   (anext a) (k (1- k)) (k2 k))))))

;; The free list after linking h in at its head (f is the free tail, and
;; g = anext[f] the old free head).
(defthm free-walk-after-link-1
  (implies (and (not (zp k))
                (aset-walk-closedp g f (1- k) a)
                (not (member-equal h (aset-walk g f (1- k) a)))
                (not (member-equal s (aset-walk g f (1- k) a)))
                (not (equal h f)))
           (equal (aset-walk h f k (as f h (as h g (as s u a))))
                  (cons h (aset-walk g f (1- k) a)))))

(defthm free-walk-after-link-2
  (implies (and (not (zp k))
                (aset-walk-closedp g f (1- k) a)
                (not (member-equal h (aset-walk g f (1- k) a)))
                (not (equal h f)))
           (equal (aset-walk h f k (as f h (as h g a)))
                  (cons h (aset-walk g f (1- k) a)))))

;;; ------------------------------------------------------------------
;;; aset_del_head, field by field.

;; The anext array after aset_del_head, with used tail s and free tail f.
(defund del-head-anext (s f a)
  (let* ((h (ag s a))
         (a1 (if (equal h s) a (as s (ag h a) a))))
    (if (< f (arr_sz))
        (as f h (as h (ag f a1) a1))
      (as h h a1))))

(defthm aset_del_head-fields
  (implies (and (natp (ag 'used_lst aset))
                (< (ag 'used_lst aset) (arr_sz))
                (natp (ag 'free_lst aset))
                (<= (ag 'free_lst aset) (arr_sz))
                (not (equal (ag 'used_lst aset) (ag 'free_lst aset))))
           (let* ((s (ag 'used_lst aset))
                  (f (ag 'free_lst aset))
                  (a (ag 'anext aset))
                  (h (ag s a)))
             (and (equal (ag 'used_lst (aset_del_head aset))
                         (if (equal h s) (arr_sz) s))
                  (equal (ag 'free_lst (aset_del_head aset))
                         (if (< f (arr_sz)) f h))
                  (equal (ag 'anext (aset_del_head aset))
                         (del-head-anext s f a)))))
  :hints (("Goal" :in-theory (enable aset_del_head aset_transfer del-head-anext
                                     log< log= true$))))

;; Used list, abstractly: h = anext[s] /= s is unlinked.
(defthm used-walk-del-head-anext
  (implies (and (natp s) (natp f) (not (equal s f)) (not (zp k))
                (not (equal (ag s a) s))
                (aset-walk-closedp (ag s a) s k a)
                (no-duplicatesp-equal (aset-walk (ag s a) s k a))
                (implies (< f (arr_sz))
                         (not (member-equal f (aset-walk (ag s a) s k a)))))
           (equal (aset-walk (ag (ag s a) a) s k
                             (del-head-anext s f a))
                  (cdr (aset-walk (ag s a) s k a))))
  :hints (("Goal" :in-theory (e/d (del-head-anext) (as-diff-as)))))

;; Free list, abstractly: h = anext[s] is linked in at the head of the
;; nonempty free list with tail f.
(defthm free-walk-del-head-anext
  (implies (and (natp s) (natp f) (not (equal s f)) (not (zp k))
                (< f (arr_sz))
                (not (equal (ag s a) f))
                (aset-walk-closedp (ag f a) f (1- k) a)
                (not (member-equal (ag s a) (aset-walk (ag f a) f (1- k) a)))
                (not (member-equal s (aset-walk (ag f a) f (1- k) a))))
           (equal (aset-walk (ag f (del-head-anext s f a)) f k
                             (del-head-anext s f a))
                  (cons (ag s a) (aset-walk (ag f a) f (1- k) a))))
  :hints (("Goal" :in-theory (e/d (del-head-anext) (as-diff-as)))))

;; Free list, abstractly, when it was empty.
(defthm free-walk-del-head-anext-empty
  (implies (and (not (zp k))
                (not (< f (arr_sz))))
           (equal (aset-walk (ag (ag s a) (del-head-anext s f a)) (ag s a) k
                             (del-head-anext s f a))
                  (list (ag s a))))
  :hints (("Goal" :in-theory (e/d (del-head-anext) (as-diff-as)))))

(defthm del-head-anext-at-s
  (implies (and (not (equal s f)) (not (equal (ag s a) s)))
           (equal (ag s (del-head-anext s f a)) (ag (ag s a) a)))
  :hints (("Goal" :in-theory (e/d (del-head-anext) ()))))

(in-theory (disable del-head-anext))

(defthm len-posp-when-consp
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)

;; Consequences of the well-formedness of the lists, in terms of the used
;; tail s, the used head h, the free tail f and the free head g.
(defthm asetp-used-facts
  (implies (and (asetp aset)
                (aset-used-to-free-preconditionp aset))
           (let* ((s (ag 'used_lst aset))
                  (f (ag 'free_lst aset))
                  (a (ag 'anext aset))
                  (h (ag s a))
                  (k (1- (arr_sz))))
             (and (natp s) (< s (arr_sz)) (natp f) (<= f (arr_sz))
                  (not (equal s f))
                  (anext-rangep 0 (arr_sz) a)
                  (equal (aset-used-list aset) (aset-walk h s k a))
                  (aset-walk-closedp h s k a)
                  (no-duplicatesp-equal (aset-walk h s k a))
                  (implies (< f (arr_sz))
                           (and (equal (aset-free-list aset)
                                       (aset-walk (ag f a) f k a))
                                (aset-walk-closedp (ag f a) f k a)
                                (not (member-equal f (aset-walk h s k a)))
                                (not (member-equal h (aset-walk (ag f a) f k a)))
                                (not (member-equal s (aset-walk (ag f a) f k a)))
                                (not (equal h f))))
                  (implies (not (< f (arr_sz)))
                           (equal (aset-free-list aset) nil)))))
  :hints (("Goal" :in-theory (enable asetp aset-used-to-free-preconditionp
                                     aset-common-preconditionp aset-lists-wfp
                                     aset-used-list aset-free-list
                                     aset-used-nonemptyp aset-free-nonemptyp
                                     )
           :use ((:instance member-tail-aset-walk
                            (idx (ag (ag 'free_lst aset) (ag 'anext aset)))
                            (tail (ag 'free_lst aset))
                            (k (1- (arr_sz)))
                            (anext (ag 'anext aset)))
                 (:instance member-tail-aset-walk
                            (idx (ag (ag 'used_lst aset) (ag 'anext aset)))
                            (tail (ag 'used_lst aset))
                            (k (1- (arr_sz)))
                            (anext (ag 'anext aset))))))
  :rule-classes nil)

(defthm aset-used-list-del-head
  (implies (and (natp (ag 'used_lst aset))
                (< (ag 'used_lst aset) (arr_sz))
                (natp (ag 'free_lst aset))
                (<= (ag 'free_lst aset) (arr_sz))
                (not (equal (ag 'used_lst aset) (ag 'free_lst aset))))
           (let* ((s (ag 'used_lst aset))
                  (f (ag 'free_lst aset))
                  (a (ag 'anext aset))
                  (h (ag s a)))
             (equal (aset-used-list (aset_del_head aset))
                    (if (equal h s)
                        nil
                      (aset-walk (ag h a) s (1- (arr_sz))
                                 (del-head-anext s f a))))))
  :hints (("Goal" :in-theory (enable aset-used-list aset-used-nonemptyp
                                     ))))

(defthm aset-free-list-del-head
  (implies (and (natp (ag 'used_lst aset))
                (< (ag 'used_lst aset) (arr_sz))
                (natp (ag 'free_lst aset))
                (<= (ag 'free_lst aset) (arr_sz))
                (not (equal (ag 'used_lst aset) (ag 'free_lst aset)))
                (anext-rangep 0 (arr_sz) (ag 'anext aset)))
           (let* ((s (ag 'used_lst aset))
                  (f (ag 'free_lst aset))
                  (a (ag 'anext aset))
                  (h (ag s a)))
             (equal (aset-free-list (aset_del_head aset))
                    (if (< f (arr_sz))
                        (aset-walk (ag f (del-head-anext s f a)) f
                                   (1- (arr_sz)) (del-head-anext s f a))
                      (aset-walk (ag h (del-head-anext s f a)) h
                                 (1- (arr_sz)) (del-head-anext s f a))))))
  :hints (("Goal" :in-theory (enable aset-free-list aset-free-nonemptyp
                                     ))))

;; The used and free lists of the arrayset have the expected total length
;; ARR_SZ - 1 (they partition the usable elements 1 .. ARR_SZ-1).
(defund aset-sizes-okp (aset)
  (= (+ (len (aset-used-list aset)) (len (aset-free-list aset)))
     (1- (ARR_SZ))))

(defthm aset_del_head-used-list
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (aset-sizes-okp aset))
   (= (aset-used-list (aset_del_head aset))
      (cdr (aset-used-list aset))))
  :hints (("Goal"
           :in-theory (e/d (aset-sizes-okp)
                           (aset-walk-open aset-walk-closedp-open))
           :use asetp-used-facts)))

(defthm aset_del_head-free-list
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (aset-sizes-okp aset))
   (= (aset-free-list (aset_del_head aset))
      (cons (used_head aset) (aset-free-list aset))))
  :hints (("Goal"
           :in-theory (e/d (aset-sizes-okp)
                           (aset-walk-open aset-walk-closedp-open))
           :use (asetp-used-facts
                 (:instance aset-walk-less-fuel
                            (idx (ag (ag 'free_lst aset) (ag 'anext aset)))
                            (tail (ag 'free_lst aset))
                            (k (1- (arr_sz)))
                            (j (- (arr_sz) 2))
                            (anext (ag 'anext aset)))))))

;;; ------------------------------------------------------------------
;;; Figure 9.  (no-dups-anext is not needed by the proofs.)

(defthm aset_del_head-used-list--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (= (+ (len (aset-used-list aset)) (len (aset-free-list aset)))
           (1- (ARR_SZ))))
   (= (aset-used-list (aset_del_head aset))
      (cdr (aset-used-list aset))))
  :hints (("Goal" :in-theory (enable aset-sizes-okp))))

(defthm aset_del_head-free-list--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (= (+ (len (aset-used-list aset)) (len (aset-free-list aset)))
           (1- (ARR_SZ))))
   (= (aset-free-list (aset_del_head aset))
      (cons (used_head aset) (aset-free-list aset))))
  :hints (("Goal" :in-theory (enable aset-sizes-okp))))
