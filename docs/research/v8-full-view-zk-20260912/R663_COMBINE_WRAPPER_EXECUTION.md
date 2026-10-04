# R663 selected `combine_beta` wrapper execution

The theorem `combine_beta_wrapper_execution` proves that the actual selected generated `query_arithmetic.combine_beta` wrapper returns `.ok (Result.Ok (laneArray lane))` when (1) the actual 104-word and 48-word `r55_decode_into` calls return the supplied arrays with `Result.Ok ()`, and (2) every actual `r83_mixed_limb` call satisfies the leaf equality required by R646. The proof unfolds the actual wrapper, preserves its nested Result/ControlFlow handling through simplification of the explicit successful decoder premises, and applies R646's complete four-slot loop theorem.

No decoder properties, leaf arithmetic, alternative failure branches under decoder failure, actual source/native theorem beyond imported generated functions, quotient interpretation, or end-to-end privacy/security result is added. R638 is imported for the existing wrapper input result context but its separate accepted-input theorem is not used to add assumptions.

The first attempt (1791114333278911000) failed because rewriting a decoder call did not match the wrapper's local `let`; the second (1791114358573046000) failed because the nested successful `Result`/`ControlFlow` branches were not simplified. Both exact source snapshots, logs, and receipts are preserved. The third attempt passed.

Green run: `1791114378370240000`; exit 0; wall 1.43 s; peak Lean-child RSS 3,762,040 KiB; swap 0. Pinned Lean 4.32 cached workspace; `-j1 -M4500`; `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Source SHA-256: `de64cbafa98451f121e0e182c1d013f3d10c9a92303410a747925568845ad206`; source revision `aa1a2d5823368175afbc95cf41666785973c2c18`. Direct imported module SHA-256 pins and complete axiom output are in the green receipt. The theorem inherits `core.fmt.Formatter` from the captured actual C1 slice/unwrap path as well as standard Lean axioms.

This remains a conditional composition theorem; the first missing proposition is the actual `r83_mixed_limb` leaf result contract, followed by the separate constructor proposition. The exact verified source and evidence are promoted together in this milestone.

All verifier source, security parameters, authentication, canonical checks, negative examples, and CU 999,790 / 999,532 are unchanged. No CU benchmark or unchanged successful regression was repeated.
