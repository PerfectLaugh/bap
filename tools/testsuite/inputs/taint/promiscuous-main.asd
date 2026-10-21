(defsystem test:promiscuous-legacy-main
  :description "The legacy main system in the promiscuous mode."
  :depends-on (bap:legacy-main)
  :components (bap:var-randomizer
               bap:mem-randomizer
               bap:arg-randomizer
               bap:promiscuous-path-explorer
               bap:division-by-zero-handler
               bap:limit))
