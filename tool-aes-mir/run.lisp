; Running the RustCrypto fixsliced AES-128 on the ACL2 MIR interpreter.
;
; (mir-aes-encrypt key block) and (mir-aes-decrypt key block) run the
; interpreter (mir/interpreter.lisp) on the imported crate's
; aes_fixslice::encrypt and aes_fixslice::decrypt (the program fixture
; mir/aes-program.lisp, which mir/import-test.lisp checks against the JSON).
; Keys and blocks are represented as in kestrel/crypto/aes/aes-spec: lists of
; 16 bytes (aes::inp).  Note the argument order: key first, as in the Rust
; entry points, whereas aes::aes-128-encrypt takes the block first.
;
; The tests below run at certification time (they are local, so including
; this book does not re-run them):
;  - FIPS-197 Appendix C.1 and Appendix B ciphertexts, byte for byte, and
;    decryption inverting both;
;  - differential tests against aes::aes-128-encrypt on 66 inputs: 2 corner
;    cases and 64 pseudorandom key/block pairs generated in-book; decryption
;    inverts the pseudorandom ciphertexts.

(in-package "ACL2")

(include-book "mir/interpreter")
(include-book "mir/aes-program")
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Entry points

(define bytes-to-mir-values (bytes)
  :returns (vs mir::value-list-p)
  (if (atom bytes)
      nil
    (cons (mir::value-int :u8 (loghead 8 (ifix (car bytes))))
          (bytes-to-mir-values (cdr bytes)))))

(define mir-values-to-bytes ((vs mir::value-list-p))
  ;; nil if some element is not a byte
  :returns (mv (ok booleanp) (bytes true-listp))
  (b* (((when (atom vs)) (mv t nil))
       (v (car vs))
       ((unless (and (mir::value-case v :int) (eq (mir::value-int->it v) :u8)))
        (mv nil nil))
       ((mv ok rest) (mir-values-to-bytes (cdr vs))))
    (mv ok (cons (mir::value-int->v v) rest))))

;; Enough for one encryption or decryption (about 77,000 steps each).
(defconst *mir-aes-fuel* 10000000)

;; Run the crate function fn (encrypt or decrypt: fn(&[u8; 16], &[u8; 16]) ->
;; [u8; 16]) with the key and the block in two static allocations.  Returns
;; the 16 result bytes, or (:mir-failure outcome) if the run does not return
;; a byte array.
(define mir-aes-run ((fn stringp) key block)
  (b* (((mv oc &)
        (mir::call-function
         fn
         (list (mir::value-ptr (mir::loc (mir::locbase-static 1) nil))
               (mir::value-ptr (mir::loc (mir::locbase-static 2) nil)))
         (list (cons 1 (mir::value-array (bytes-to-mir-values key)))
               (cons 2 (mir::value-array (bytes-to-mir-values block))))
         *mir-aes-fuel*
         mir::*aes-program*))
       ((unless (mir::outcome-case oc :returned)) (list :mir-failure oc))
       (v (mir::outcome-returned->v oc))
       ((unless (mir::value-case v :array)) (list :mir-failure oc))
       ((mv ok bytes) (mir-values-to-bytes (mir::value-array->elems v))))
    (if ok bytes (list :mir-failure oc))))

(define mir-aes-encrypt (key block)
  (mir-aes-run "aes_fixslice::encrypt" key block))

(define mir-aes-decrypt (key block)
  (mir-aes-run "aes_fixslice::decrypt" key block))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FIPS-197 known-answer tests

;; Appendix C.1 (AES-128)
(defconst *c1-key* '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07
                     #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f))
(defconst *c1-plaintext* '(#x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77
                           #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff))
(defconst *c1-ciphertext* '(#x69 #xc4 #xe0 #xd8 #x6a #x7b #x04 #x30
                            #xd8 #xcd #xb7 #x80 #x70 #xb4 #xc5 #x5a))

;; Appendix B (cipher example)
(defconst *b-key* '(#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6
                    #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c))
(defconst *b-plaintext* '(#x32 #x43 #xf6 #xa8 #x88 #x5a #x30 #x8d
                          #x31 #x31 #x98 #xa2 #xe0 #x37 #x07 #x34))
(defconst *b-ciphertext* '(#x39 #x25 #x84 #x1d #x02 #xdc #x09 #xfb
                           #xdc #x11 #x85 #x97 #x19 #x6a #x0b #x32))

(local (assert-event (equal (mir-aes-encrypt *c1-key* *c1-plaintext*) *c1-ciphertext*)))
(local (assert-event (equal (mir-aes-decrypt *c1-key* *c1-ciphertext*) *c1-plaintext*)))
(local (assert-event (equal (mir-aes-encrypt *b-key* *b-plaintext*) *b-ciphertext*)))
(local (assert-event (equal (mir-aes-decrypt *b-key* *b-ciphertext*) *b-plaintext*)))

;; The same vectors agree with the specification.
(local (assert-event (equal (aes::aes-128-encrypt *c1-plaintext* *c1-key*) *c1-ciphertext*)))
(local (assert-event (equal (aes::aes-128-encrypt *b-plaintext* *b-key*) *b-ciphertext*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Differential tests against the ACL2 AES-128 specification

;; A pseudorandom byte stream: a 32-bit xorshift generator.
(define xorshift32 ((x natp))
  :returns (y natp :rule-classes :type-prescription)
  (b* ((x (loghead 32 (lnfix x)))
       (x (loghead 32 (logxor x (ash x 13))))
       (x (logxor x (ash x -17)))
       (x (loghead 32 (logxor x (ash x 5)))))
    x))

(define prng-bytes ((n natp) (seed natp))
  ;; n bytes from the generator, and the next seed
  :returns (mv (bytes true-listp) (seed2 natp :rule-classes :type-prescription))
  (if (zp n)
      (mv nil (lnfix seed))
    (b* ((s (xorshift32 seed))
         ((mv rest s2) (prng-bytes (1- n) s)))
      (mv (cons (loghead 8 (ash s -24)) rest) s2))))

;; n pseudorandom (key . block) pairs.
(define prng-pairs ((n natp) (seed natp))
  :returns (pairs true-listp)
  (if (zp n)
      nil
    (b* (((mv key seed) (prng-bytes 16 seed))
         ((mv block seed) (prng-bytes 16 seed)))
      (cons (cons key block) (prng-pairs (1- n) seed)))))

(defconst *corner-pairs*
  (list (cons (repeat 16 0) (repeat 16 0))
        (cons (repeat 16 255) (repeat 16 255))))

(defconst *random-pairs* (prng-pairs 64 2026))

(defconst *differential-pairs* (append *corner-pairs* *random-pairs*))

(assert-event (and (equal (len *differential-pairs*) 66)
                   (no-duplicatesp-equal *differential-pairs*)))

;; The inputs on which encryption disagrees with the specification.
(define encrypt-mismatches ((pairs alistp))
  (if (atom pairs)
      nil
    (b* ((key (car (car pairs)))
         (block (cdr (car pairs)))
         (rest (encrypt-mismatches (cdr pairs))))
      (if (and (aes::inp key) (aes::inp block)
               (equal (mir-aes-encrypt key block)
                      (aes::aes-128-encrypt block key)))
          rest
        (cons (car pairs) rest)))))

;; The inputs on which decryption disagrees with the specification.
(define decrypt-spec-mismatches ((pairs alistp))
  (if (atom pairs)
      nil
    (b* ((key (car (car pairs)))
         (block (cdr (car pairs)))
         (rest (decrypt-spec-mismatches (cdr pairs))))
      (if (and (aes::inp key) (aes::inp block)
               (equal (mir-aes-decrypt key block)
                      (aes::aes-128-decrypt block key)))
          rest
        (cons (car pairs) rest)))))

;; The inputs whose ciphertext decryption does not invert.
(define decrypt-mismatches ((pairs alistp))
  (if (atom pairs)
      nil
    (b* ((key (car (car pairs)))
         (block (cdr (car pairs)))
         (rest (decrypt-mismatches (cdr pairs))))
      (if (and (aes::inp key) (aes::inp block)
               (equal (mir-aes-decrypt key (aes::aes-128-encrypt block key))
                      block))
          rest
        (cons (car pairs) rest)))))

(local (assert-event (null (encrypt-mismatches *differential-pairs*))))

(local (assert-event (null (decrypt-mismatches *random-pairs*))))

;; Beyond the paper's checks: decryption also agrees with aes::aes-128-decrypt.
(local (assert-event (null (decrypt-spec-mismatches *differential-pairs*))))
