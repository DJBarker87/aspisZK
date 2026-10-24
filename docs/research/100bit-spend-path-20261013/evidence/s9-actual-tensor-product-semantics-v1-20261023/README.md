# Actual tensor product semantics

**Proved:** `S9ActualTensorOuterSemanticsV1.actual_tensor_s2_success_high_product` interprets the SAME native actual32 S2 tensor accepted execution, including reverse in-place writes and initialization of arbitrary scratch. Each successfully read output i<64 decodes to `factor 2 (i%4) * factor 3 ((i/4)%4) * factor 4 ((i/16)%4)`.

The explicit INPUT contract identifies what actual successful stored factor reads mean and proves their canonicality. It assumes no tensor/output equality or child success. Constructor factor semantics must supply that contract; mathematical correctness of the stored constructor factors is NOT established here. The actual arithmetic operation interpretation reuses existing native-to-helper full Result transport and CurrentQM multiplication semantics. Native ONE is interpreted as1.

Six focused targets prove source update framing/meaning, symbolic digit partitioning, exact native body multiplication/write semantics, the whole reverse loop invariant, and the three widths1→4→16→64. No64-cell recurrence is unfolded. Canonicality is retained separately to justify primitive field interpretation, not used as a substitute for algebra.

Existing D18 radix-four/Boolean row identities are exact reuse targets, not re-proved or claimed newly composed. Remaining: constructor factors/statement-point mathematical correspondence, circle rows, complete pairing equations, caller/source/runtime/Box normalization and final frozen release artifacts/security composition. Target not yet established.

All6focused targets passed -M4400/one thread under atomic local mutex,7.5GiB aggregate stop/120s watchdog, standard axioms and zero swap. Exact source/revision/receipts/commands/profiles/object selections retained. Failed predecessors and two preflight-only missing-object attempts retained. No binaries/full inventories/final replay.
