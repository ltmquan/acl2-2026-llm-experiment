(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUND ARR_SZ NIL 1024)

(DEFUND FREE_HEAD (ASET)
  (LET ((RETVAL (ARR_SZ)))
    (IF1 (LOG< (AG 'FREE_LST ASET) (ARR_SZ))
         (AG (AG 'FREE_LST ASET)
             (AG 'ANEXT ASET))
         RETVAL)))

(DEFUND USED_HEAD (ASET)
  (LET ((RETVAL (ARR_SZ)))
    (IF1 (LOG< (AG 'USED_LST ASET) (ARR_SZ))
         (AG (AG 'USED_LST ASET)
             (AG 'ANEXT ASET))
         RETVAL)))

(DEFUND ASET_INIT-LOOP-0 (I ASET)
  (DECLARE (XARGS :MEASURE (NFIX (- (ARR_SZ) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP (ARR_SZ))
           (< I (ARR_SZ)))
      (LET* ((ASET (AS 'AVALS
                       (AS I (BITS 0 63 0) (AG 'AVALS ASET))
                       ASET))
             (ASET (IF1 (LOG= I 0)
                        (AS 'ANEXT
                            (AS I 0 (AG 'ANEXT ASET))
                            ASET)
                        (IF1 (LOG= I (- (ARR_SZ) 1))
                             (AS 'ANEXT
                                 (AS I (BITS 1 63 0) (AG 'ANEXT ASET))
                                 ASET)
                             (AS 'ANEXT
                                 (AS I (+ I 1) (AG 'ANEXT ASET))
                                 ASET)))))
        (ASET_INIT-LOOP-0 (+ I 1) ASET))
    ASET))

(DEFUND ASET_INIT (ASET)
  (LET* ((ASET (ASET_INIT-LOOP-0 0 ASET))
         (ASET (AS 'FREE_LST (- (ARR_SZ) 1) ASET))
         (ASET (AS 'USED_LST (ARR_SZ) ASET)))
    (AS 'ERR (BITS 1 63 0) ASET)))

(DEFUND ASET_TRANSFER (USED_TO_FREE ASET)
 (LET ((SRC (AG 'FREE_LST ASET))
       (DST (AG 'USED_LST ASET)))
  (MV-LET (SRC DST)
          (IF1 USED_TO_FREE
               (MV (AG 'USED_LST ASET)
                   (AG 'FREE_LST ASET))
               (MV SRC DST))
    (MV-LET
          (SRC DST ASET)
          (IF1 (LOG< SRC (ARR_SZ))
               (LET ((HD (AG SRC (AG 'ANEXT ASET))))
                 (MV-LET (ASET SRC)
                         (IF1 (LOG= HD SRC)
                              (MV ASET (ARR_SZ))
                              (MV (AS 'ANEXT
                                      (AS SRC (AG HD (AG 'ANEXT ASET))
                                          (AG 'ANEXT ASET))
                                      ASET)
                                  SRC))
                   (MV-LET (DST ASET)
                           (IF1 (LOG< DST (ARR_SZ))
                                (LET ((ASET (AS 'ANEXT
                                                (AS HD (AG DST (AG 'ANEXT ASET))
                                                    (AG 'ANEXT ASET))
                                                ASET)))
                                  (MV DST
                                      (AS 'ANEXT
                                          (AS DST HD (AG 'ANEXT ASET))
                                          ASET)))
                                (MV HD
                                    (AS 'ANEXT
                                        (AS HD HD (AG 'ANEXT ASET))
                                        ASET)))
                     (MV SRC DST
                         (AS 'ERR
                             (BITS 1 63 0)
                             (IF1 USED_TO_FREE
                                  (LET ((ASET (AS 'USED_LST SRC ASET)))
                                    (AS 'FREE_LST DST ASET))
                                  (LET ((ASET (AS 'FREE_LST SRC ASET)))
                                    (AS 'USED_LST DST ASET))))))))
               (MV SRC DST (AS 'ERR (ARR_SZ) ASET)))
      ASET))))

(DEFUND ASET_ADD (VAL ASET)
  (LET ((IDX (ARR_SZ))
        (ASET (ASET_TRANSFER (FALSE$) ASET)))
    (IF1 (LOG= (AG 'ERR ASET) 1)
         (AS 'AVALS
             (AS (AG (AG 'USED_LST ASET)
                     (AG 'ANEXT ASET))
                 (BITS (SI VAL 64) 63 0)
                 (AG 'AVALS ASET))
             ASET)
         ASET)))

(DEFUND ASET_DEL_HEAD (ASET)
  (LET ((IDX 0))
    (ASET_TRANSFER (TRUE$) ASET)))

(DEFUND ASET_FIND_VAL_FROM-LOOP-0 (I ASET VAL START IDX RETVAL DONE)
  (DECLARE (XARGS :MEASURE (NFIX (- (ARR_SZ) I))))
  (IF (AND (INTEGERP I)
           (INTEGERP (ARR_SZ))
           (AND (< I (ARR_SZ)) (EQL DONE 0)))
      (LET ((NXT (AG IDX (AG 'ANEXT ASET))))
        (MV-LET (IDX RETVAL DONE)
                (IF1 (LOG= (SI (AG NXT (AG 'AVALS ASET)) 64)
                           (SI VAL 64))
                     (MV IDX IDX (TRUE$))
                     (MV-LET (IDX DONE)
                             (IF1 (LOG= NXT START)
                                  (MV IDX (TRUE$))
                                  (MV NXT DONE))
                       (MV IDX RETVAL DONE)))
          (ASET_FIND_VAL_FROM-LOOP-0 (+ I 1)
                                     ASET VAL START IDX RETVAL DONE)))
    (MV IDX RETVAL DONE)))

(DEFUND ASET_FIND_VAL_FROM (START VAL ASET)
  (LET ((RETVAL (ARR_SZ))
        (IDX START)
        (DONE (LOGNOT1 (LOG< START (ARR_SZ)))))
    (MV-LET (IDX RETVAL DONE)
            (ASET_FIND_VAL_FROM-LOOP-0 0 ASET VAL START IDX RETVAL DONE)
      RETVAL)))

(DEFUND ASET_DEL (VAL ASET)
  (LET ((PREV_INDEX (ARR_SZ)))
    (MV-LET (PREV_INDEX ASET)
            (IF1 (LOG< (AG 'USED_LST ASET) (ARR_SZ))
                 (LET ((PREV_INDEX (ASET_FIND_VAL_FROM (AG 'USED_LST ASET)
                                                       (BITS (SI VAL 64) 63 0)
                                                       ASET)))
                   (MV PREV_INDEX
                       (IF1 (LOGAND1 (LOG< PREV_INDEX (ARR_SZ))
                                     (LOG<> PREV_INDEX (AG 'FREE_LST ASET)))
                            (LET ((ASET (AS 'USED_LST PREV_INDEX ASET)))
                              (ASET_DEL_HEAD ASET))
                            (AS 'ERR (ARR_SZ) ASET))))
                 (MV PREV_INDEX (AS 'ERR (ARR_SZ) ASET)))
      ASET)))

