# R346 — exact selected branch after guards

`AspisR346AfterGuardsRaw.lean` compiled successfully. The literal contiguous selected R292 else branch, lines 527–605, compiles with the exact copied seven-constructor Error declaration. It retains prefix initialization, last-value reads, shared inverse, both output setups, reverse loops, index-zero writes, and the nested success result. This is an executable raw-source fragment, not an execution correspondence theorem. Guard evaluation is excluded. Imported pinned Aeneas Std behavior and compiler correspondence are separate obligations.

Compile revision `56a931fc3879354a2fa584e73bd0a1d412714851`; exit 0; wall 0:01.11; child peak RSS 2540904 KiB; swaps 0. Error has no axioms; selectedAfterGuards uses only propext, Classical.choice and Quot.sound. No execution assumption, sorryAx or native axiom appears. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r346-current-after-guards-raw/manifest.json).

First remaining proposition: Prove an unconditional error-preserving decomposition into the already verified prefix, shared-inverse and output fragments, then their complete conditional execution under explicit canonical nonempty inputs. Prove the actual enclosing guard and unresolved source-library traversal separately.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
