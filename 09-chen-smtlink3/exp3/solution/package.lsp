; Smtlink 3 (reimplementation) -- package definition
(defpkg "SMT"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            '(pseudo-termp pseudo-term-listp pseudo-term-list-listp
              disjoin disjoin2 conjoin conjoin2 conjoin-clauses disjoin-lst
              clauses-result dumb-negate-lit flambda-applicationp
              lambda-applicationp fquotep unquote
              b* rewrite$ getpropc fgetprop access rewrite-rule
              value er-let* er-progn trans-eval simple-translate-and-eval
              translate translate-hints translate-term-lst
              add-custom-keyword-hint add-default-hints! set-default-hints!
              def-ruleset defttag sys-call+ str-fix
              define-trusted-clause-processor
              strip-cars strip-cadrs all-vars all-vars1
              msg fms fmt fmt1 cw cw! cw+ untranslate
              *t* *nil* fcons-term* cons-term
              variablep ffn-symb fargs fn-symb explode-atom table-alist
              packn packn-pos intersectp-equal add-to-set-equal strip-cdrs
              remove1-assoc-equal flambdap lambda-body lambda-formals
              getprop global-val ens enabled-runep current-theory
              union-theories theory fargn quotep evens keyword-value-listp
              subsetp-eq remove-duplicates-eq remove-duplicates-equal)))
