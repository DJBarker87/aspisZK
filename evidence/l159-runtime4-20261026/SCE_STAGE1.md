# Stage 1: one adversary and exact byte projection

SCE_Experiment.Adversary contains only a first submission program and the
response-driven second submission. Both are fixed before H; entries, results
and traces are outputs. SCE_Experiment.runtime records the actual configured
GExq account program and computes acceptance from BOTH wrapper replies.
SCE_Experiment.submission uses the original first buffers (public account1,
proof account0 after 688 bytes), not an independently supplied ByteProver.

SCE_Projection.input_projection/stored/byte_observation establish the exact
same-H stored association with no admission, byte-equality or source law as
input. Rejection prefixes remain visible. chronological retains the full
actual log. The full physical/source and annotation joins are NOT yet proved.

Quantifier change is explicit: (forall P runtime, R P runtime) is replaced by
(forall a, R (submission a) (runtime a)). SCE_Quantifiers.deployed_iff proves
this exactly equivalent to the former independent-binder form restricted to
the image of actual shared-adversary constructions. old_use provides the
backward application at any such pair. It does not imply the false unrestricted
statement or assert every pair lies in that image. The image equality is not
claimed as an assumption discharge or a source refinement.

Attempts 001–003 passed, standard axioms only, exact receipts retained. Initial
001 reservation denied; waited at least 3 minutes and retry1 admitted. No
compile was launched on denial. Budget: 3/100 Lean, 0/10 Kani. Actual Rc5 root
unchanged; L159/L185 not yet removed. New byte projection is a proved precursor.
