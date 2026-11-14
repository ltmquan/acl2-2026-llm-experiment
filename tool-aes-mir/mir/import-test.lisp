; MIR semantics: import test.
;
; Parses the committed ULLBC JSON sample (../subject/aes_fixslice.ullbc) at
; certification time and checks that the importer's result is exactly the
; program fixture *aes-program* (aes-program.lisp) that the interpreter
; tests run on.

(in-package "MIR")

(include-book "import-json")
(include-book "aes-program")

(defconsts (*imported-err* *imported-program* state)
  (time$ (import-ullbc-file "../subject/aes_fixslice.ullbc" state)))

(assert-event (null *imported-err*))

(assert-event (program-p *imported-program*))

(assert-event (equal *imported-program* *aes-program*))

;; A few sanity checks on the shape of the imported crate.
(assert-event (equal (program->crate *aes-program*) "aes_fixslice"))

(assert-event (natp (program-find-fun "aes_fixslice::encrypt" *aes-program*)))

(assert-event (natp (program-find-fun "aes_fixslice::decrypt" *aes-program*)))
