# R260 complete private input execution

`AspisV8R19/R260PrivateInputExecution.lean` compiled successfully. The emitted Option branch returns Continue/Break exactly; its emitted residual assertion succeeds for all Option<Infallible> values (the Some case is impossible by the empty source type). The actual private C::input succeeds with Some exactly when both raw coordinates are below P, otherwise with None, preserving both short-circuit branches. Canonical encoded complex values return Some of the exact encoded pair. No coefficients, batch, callback trace, acceptance or security result.

Compile revision `2792ad7dcbaa1176b71d3174da3f0675ec58c159`; exit 0; wall 0:01.58; child peak RSS 3707096 KiB; swaps 0. Complete reports are either axiom-free or use only propext, Classical.choice and Quot.sound. No sorryAx, native decision axiom or new execution premise. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r260-current-private-input-execution/manifest.json).

First remaining proposition: Bind private Coeff110 execution, actual inverse batch/traversal and optimized-to-source acceptance; complete callback trace, shared-oracle law, joint privacy and soundness remain open.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
