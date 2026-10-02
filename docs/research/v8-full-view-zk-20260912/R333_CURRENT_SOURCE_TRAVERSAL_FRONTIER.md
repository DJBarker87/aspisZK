# R333: actual source traversal frontier

R327 extraction exposed both selected `Iterator::try_fold` bodies and the three selected `ControlFlow` methods. The source root and its decoded body remain unchanged; 21 reachable opaque helpers remain. Extraction exited 0 in 13.47 seconds, peak RSS 626,232 KiB, zero swaps.

The R330 translation exited 2 in 0.16 seconds, peak RSS 64,768 KiB, zero swaps. It emitted no Lean files. Its first failure is `Nested-loop returns require exactly one Option language item`: the monomorphized input contains three concrete Option types, none for the pending ControlFlow return. No concrete Option was substituted, source constraint removed, or opaque execution premise introduced. The earlier R303 erased-region failure remains historical. R323 establishes that pinned Charon uses nightly-2026-06-01, correcting the earlier runner's stable-toolchain attribution.

[Exact reviewed evidence](evidence/r333-source-traversal-frontier/frontier-manifest.json) includes source/tool hashes, revisions, commands, caps, complete logs, inventories and correction history. `#print axioms` is not applicable: no Lean output was generated. An initial numeric-ID-only comparison was overwritten; that missing predecessor is disclosed, and the corrected identity-based comparison is preserved.

First remaining proposition: faithful original traversal and closure execution with every stop/error and unchanged source constraints. Prefix/inverse fragment proofs do not prove the surrounding guard or independent compiler/standard-library correspondence. Whole callback chronology, privacy and soundness remain unproved. The verifier, all security parameters, and 999,790 / 999,532 CU remain preserved; no benchmarks or unchanged regression suites reran.
