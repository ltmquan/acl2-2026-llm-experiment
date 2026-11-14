; Grader R5 (tool-aes-mir): 66 inputs of our own, run through the adapter,
; agree with aes::aes-128-encrypt:
;   2 corner cases: all-zero key and block; all-#xff key and block;
;   64 pseudorandom key/block pairs from splitmix64 with the fixed seed
;   #x4752414445522D44 (ASCII "GRADER-D"): pair i uses the generator outputs
;   4i .. 4i+3, each split into 8 bytes little-endian; key = bytes 0..15,
;   block = bytes 16..31.
(in-package "ACL2")
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)
(include-book "grader-aes-adapter")

(program)

(defconst *gr-seed* #x4752414445522D44)
(defconst *gr-m64* (expt 2 64))

; splitmix64: state += golden gamma; output = mix(state)
(defun gr-sm64-mix (z)
  (let* ((z (mod (* (logxor z (ash z -30)) #xBF58476D1CE4E5B9) *gr-m64*))
         (z (mod (* (logxor z (ash z -27)) #x94D049BB133111EB) *gr-m64*)))
    (logxor z (ash z -31))))

(defun gr-sm64-outputs (n state64)
  ;; the next n outputs
  (if (zp n)
      nil
    (let ((s (mod (+ state64 #x9E3779B97F4A7C15) *gr-m64*)))
      (cons (gr-sm64-mix s) (gr-sm64-outputs (1- n) s)))))

(defun gr-u64-bytes (w k)
  (if (zp k) nil (cons (logand w #xff) (gr-u64-bytes (ash w -8) (1- k)))))

(defun gr-words-bytes (ws)
  (if (endp ws) nil (append (gr-u64-bytes (car ws) 8) (gr-words-bytes (cdr ws)))))

(defun gr-pairs (ws)
  ;; groups of 4 words -> (key . block)
  (if (or (endp ws) (endp (cdr ws)) (endp (cddr ws)) (endp (cdddr ws)))
      nil
    (let ((bytes (gr-words-bytes (list (first ws) (second ws) (third ws) (fourth ws)))))
      (cons (cons (take 16 bytes) (nthcdr 16 bytes))
            (gr-pairs (nthcdr 4 ws))))))

(defconst *gr-inputs*
  (append (list (cons (repeat 16 0) (repeat 16 0))
                (cons (repeat 16 #xff) (repeat 16 #xff)))
          (gr-pairs (gr-sm64-outputs 256 *gr-seed*))))

(defun gr-check (inputs i)
  ;; list of indices where the interpreter disagrees with the specification
  (if (endp inputs)
      nil
    (let* ((key (car (car inputs)))
           (blk (cdr (car inputs)))
           (got (grader-aes-encrypt key blk))
           (exp (aes::aes-128-encrypt blk key)))
      (if (equal got exp)
          (gr-check (cdr inputs) (1+ i))
        (prog2$ (cw "GRADER-FAIL input ~x0: key ~x1 block ~x2 expected ~x3 got ~x4~%" i key blk exp got)
                (cons i (gr-check (cdr inputs) (1+ i))))))))

(logic)

(assert-event (equal (len *gr-inputs*) 66))
(assert-event (and (aes::inp (cdr (nth 65 *gr-inputs*))) (aes::keyp (car (nth 65 *gr-inputs*)) 4)))
; the first generated key, recorded in NOTES.md, so that the inputs can be reproduced
(value-triple (cw "GRADER: first pseudorandom pair ~x0~%" (nth 2 *gr-inputs*)))

(assert-event (null (gr-check *gr-inputs* 0))
              :msg "GRADER-FAIL: the interpreter disagrees with aes::aes-128-encrypt (see above)")
(value-triple (cw "GRADER-OK all 66 inputs agree~%"))
