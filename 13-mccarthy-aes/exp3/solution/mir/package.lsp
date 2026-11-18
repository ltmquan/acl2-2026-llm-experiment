; MIR semantics: package definition.

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

(defpkg "MIR" (append (set-difference-eq *std-pkg-symbols*
                                         '(value values step program
                                           function functionp))
                      '(b* define defines defret defrule defruled
                        fty::deftypes fty::defprod fty::deftagsum fty::deflist
                        fty::defalist fty::defoption fty::defenum fty::deffixtype
                        maybe-natp maybe-integerp
                        parsed-json-valuep
                        assert-event with-guard-checking-event
                        ifix nfix lnfix lifix loghead logext logand logior logxor
                        lognot ash
                        str::cat
                        nat-listp str-fix bool-fix maybe-natp-fix symbol-fix
                        hons-acons hons-get fast-alist-free fast-alist-fork
                        defthm-parsed-json)))
