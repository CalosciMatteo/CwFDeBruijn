- f_equiv does not work with transport and ftm
    (it finds the propositional equality instance).
  use
  ` refine (proper_transport _ _ _ _ _ _ _ _ _)` and
  `proper_morphism (ftm[ _])` instead