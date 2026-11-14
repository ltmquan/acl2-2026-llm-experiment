; Grader R4 (tool-aes-mir): the interpreter, run through the adapter written
; from the model's README, reproduces the FIPS-197 AES-128 ciphertexts of
; Appendix C.1 and Appendix B byte for byte, and decrypt inverts both.
; The vectors are transcribed from FIPS-197; they are first checked against
; aes::aes-128-encrypt, so the expected values do not rest on the transcription.
(in-package "ACL2")
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)
(include-book "grader-aes-adapter")

; FIPS-197 Appendix C.1 (AES-128)
(defconst *gr-c1-key*   '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f))
(defconst *gr-c1-plain* '(#x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff))
(defconst *gr-c1-ciph*  '(#x69 #xc4 #xe0 #xd8 #x6a #x7b #x04 #x30 #xd8 #xcd #xb7 #x80 #x70 #xb4 #xc5 #x5a))
; FIPS-197 Appendix B (cipher example)
(defconst *gr-b-key*    '(#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6 #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c))
(defconst *gr-b-plain*  '(#x32 #x43 #xf6 #xa8 #x88 #x5a #x30 #x8d #x31 #x31 #x98 #xa2 #xe0 #x37 #x07 #x34))
(defconst *gr-b-ciph*   '(#x39 #x25 #x84 #x1d #x02 #xdc #x09 #xfb #xdc #x11 #x85 #x97 #x19 #x6a #x0b #x32))

; the transcription agrees with the specification (argument order: plaintext, key)
(assert-event (equal (aes::aes-128-encrypt *gr-c1-plain* *gr-c1-key*) *gr-c1-ciph*))
(assert-event (equal (aes::aes-128-decrypt *gr-c1-ciph* *gr-c1-key*) *gr-c1-plain*))
(assert-event (equal (aes::aes-128-encrypt *gr-b-plain* *gr-b-key*) *gr-b-ciph*))
(assert-event (equal (aes::aes-128-decrypt *gr-b-ciph* *gr-b-key*) *gr-b-plain*))

; the interpreter (adapter argument order: key, block)
(assert-event (equal (grader-aes-encrypt *gr-c1-key* *gr-c1-plain*) *gr-c1-ciph*)
              :msg "GRADER-FAIL: encrypt on FIPS-197 C.1")
(assert-event (equal (grader-aes-decrypt *gr-c1-key* *gr-c1-ciph*) *gr-c1-plain*)
              :msg "GRADER-FAIL: decrypt on FIPS-197 C.1")
(assert-event (equal (grader-aes-encrypt *gr-b-key* *gr-b-plain*) *gr-b-ciph*)
              :msg "GRADER-FAIL: encrypt on FIPS-197 B")
(assert-event (equal (grader-aes-decrypt *gr-b-key* *gr-b-ciph*) *gr-b-plain*)
              :msg "GRADER-FAIL: decrypt on FIPS-197 B")
