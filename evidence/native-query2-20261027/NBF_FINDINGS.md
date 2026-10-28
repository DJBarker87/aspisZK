# Caller-domain findings and exclusions

These are proof coverage findings, not shipped verifier bugs or changed trust.

1. Native Vec row/initialization/value/tail context gates use actual arbitrary
   backing contents at length64 and allocation capacity64. The model frame is
   generic in vector length, but native capacity-parametric extension or the
   exact adopted allocation-capacity law has not been separately installed.
   Until derived from every SAME reached constructor (or a proved capacity
   independence law), do not promote these gates to arbitrary Vec contexts.
2. K005 witnesses unobserved prepared/g/proof fields and smaller unused state;
   K014–K017 broaden row/weight states and fold/decoded outputs but time out.
   Neither establishes every actual query caller domain. Their independent
   existence does not form an enclosing same-execution certificate.
3. K013 proves one mutable suffix write at an arbitrary global offset. It
   does not establish the actual full Enumerate counter/back-continuation
   interpretation. Full native finish association remains OPEN.
4. NBF_QueryLoop.from_constructors is a model-side accepted-run phase/power
   projection with explicit NBC_Qm31Canonical and prepared rho hypotheses.
   It is not a complete source-to-model or source-to-ELF refinement, and it
   removes no headline premise. Native field/dots/fold/geometry/producer
   dictionary installation and attempted-prefix effects remain as named.
