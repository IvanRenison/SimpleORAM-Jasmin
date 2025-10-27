require import SimpleORAM.


lemma EC_security :
  equiv[
    SimpleORAM.ORAM.compile ~ SimpleORAM.ORAM.compile :
      true ==> SimpleORAM.ORAM.leakage{1} = SimpleORAM.ORAM.leakage{2}
  ].
admitted.
