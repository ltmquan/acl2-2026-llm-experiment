; grader-aes-adapter.lisp -- TEMPLATE.  A person writes this file for one
; submission, from the invocation the model's /work/README.md documents, and
; passes it to grade.sh with --adapter (override; see CHECKLIST.md, R5/R6).  It is copied
; to the root of the work copy, so include-book paths are relative to /work.
;
; It must define, in the ACL2 package, two functions (program mode is fine)
; that run the model's MIR interpreter on the imported crate:
;   (grader-aes-encrypt key block) -> the ciphertext, a list of 16 bytes
;   (grader-aes-decrypt key block) -> the plaintext, a list of 16 bytes
; where key and block are lists of 16 bytes (naturals below 256), and return
; anything else (e.g. :failed) when the run does not finish normally.
; Only conversions between byte lists and the model's value representation and
; the call of the model's documented entry point belong here: no AES code.
;
; Example (for an interpreter like the one the paper describes; adapt names):
;
; (in-package "ACL2")
; (include-book "acl2/mir/interp")                 ; the model's interpreter
; (include-book "acl2/mir/tests/aes-program")      ; the model's imported program
; (program)
; (defun grader-u8-values (bytes)
;   (if (endp bytes) nil
;     (cons (rust::value-uint (car bytes) (rust::uint-type-u8))
;           (grader-u8-values (cdr bytes)))))
; (defun grader-bytes-of (v) ...)                  ; value -> byte list
; (defun grader-aes-run (name key block)
;   (let ((out (rust::run-fn name (list (rust::value-array (grader-u8-values key))
;                                       (rust::value-array (grader-u8-values block)))
;                            rust::*aes-program* 10000000)))
;     (if (rust::runout-case out :done) (grader-bytes-of (rust::runout-done->value out)) :failed)))
; (defun grader-aes-encrypt (key block) (grader-aes-run "encrypt" key block))
; (defun grader-aes-decrypt (key block) (grader-aes-run "decrypt" key block))
