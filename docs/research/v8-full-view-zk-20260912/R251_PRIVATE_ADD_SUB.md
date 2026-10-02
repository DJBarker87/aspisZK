# R251 private canonical addition and subtraction

`AspisV8R19/R251PrivateAddSub.lean` compiled successfully. Private B::add/sub on raw canonical inputs succeed, return the exact modular value, and preserve canonical range. On field encodings they return encoded field addition/subtraction. Raw wrapping and guarded finish are preserved. No private complex product, coefficients, batch, callback or acceptance theorem.

Compile revision `27306b5980406d9912b4664d97c2d35b6e2881e2`; exit 0; wall 0:01.59; child peak RSS 3713320 KiB; swaps 0. All complete reports use only propext, Classical.choice and Quot.sound. No sorryAx, native decision axiom or new execution premise. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r251-current-private-add-sub/manifest.json).

First remaining proposition: Prove private complex product/square/input and Coeff110, actual batch/traversal and optimized-to-source acceptance.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
