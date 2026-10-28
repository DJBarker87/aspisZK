# NBA stage 5: decoder and query transcript

L030 constructs the exact ordered eight masked words from every typed byte
block. L033 proves generic eight-slot reads and list decomposition. L035
proves the complete first-stop driver's equality to the generic list walk,
including decoder and finish errors and fallback advance7.

K022 supersedes K018 after the aligned powers-return harness correction.
K023 passes native eager materialization: SAME live oracle, absorbed state,
all16 squeeze/advance calls, input framing, every returned byte and all slots.
K024 passes both decoder Result branches: error maps to Transcript and retains
the absorbed state; success returns every query and selected state. Both
branches and the eager decoder cut are covered. The return abstraction has
arbitrary error accepted-count, arbitrary queries and selected state. No
successful core decoder equation or field arithmetic is assumed by the gate.

L029, L031, L032, L034 were local elaboration errors, retained in full. Repairs
only add monadic normalization, explicit dependent witnesses and tiny eight-
index cases; no timeout, memory cap, axiom or imported definition changed.

Still open at this stage: native/model sampler scalar and rho association,
cohort materialization construction, full composite trace and caller domains.
No CLOSED composite or headline premise-removal claim is made.
