; Regenerate aes-program.lisp, the committed program fixture, from the ULLBC
; JSON (run by gen-program.sh; not a book).
(include-book "import-json")
(include-book "kestrel/file-io-light/write-objects-to-file" :dir :system)
(in-package "MIR")
(defconsts (*err* *prog* state)
  (import-ullbc-file "../subject/aes_fixslice.ullbc" state))
(assert-event (null *err*))
(acl2::write-objects-to-file
 (list '(in-package "MIR")
       '(include-book "syntax")
       (list 'defconst '*aes-program* (list 'quote *prog*))
       '(assert-event (program-p *aes-program*)))
 "aes-program.body" 'gen-program state)
