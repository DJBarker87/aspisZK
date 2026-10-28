# Query source association work

Frozen query driver is eager: one absorb and sixteen read/advance digests
occur before queries_from_pairs scans. Early scan stop selects its SAME earlier
advance; trailing digest calls still occurred. NBA query materialization/result
harnesses check this whole effect ordering with arbitrary oracle replies, using
an overapproximated decoder return. Their proofs are pending at this checkpoint.

The callee is decomposed into ONE native masked-word callback (K015), ONE
native QueryScan word update (K013), ONE outer-driver iteration (K016), and
actual finish (K014). These use the actual private QueryScan type. The source
contains call is the existing pure TrustedStd contract, bound to the SAME
accepted prefix by NBA_QueryStep. Its Frame has exact draw/length values and
the entire array, not just a decoded prefix.

NBA_QueryTrace.source/unique (L024) induct those Frames to exact source-shaped
scanListLoop Result. NBA_QueryConstruct.construct (L026) builds a trace from
EVERY bounded state and finite word list; no scan result hypothesis occurs.
The from_fn/masked-byte totality and first-stop driver ports are being completed
before decoder substitution may receive CLOSED credit. No XRn kit is used.

Final update: K023/K024 eager wrapper and both Result/state branches PASS; NBA_Materialize.source and NBA_QueryJoin.source PASS. The complete native query child association remains part of the OPEN composite join. See NBA_prepare_BRIDGE.md.
