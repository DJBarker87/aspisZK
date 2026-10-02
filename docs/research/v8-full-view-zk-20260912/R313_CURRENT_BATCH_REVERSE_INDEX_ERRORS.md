# R313: selected reverse-body index errors

`AspisV8R19/R313BatchReverseIndexErrors.lean` compiled successfully. Against the pinned executable Aeneas library, the unchanged generated reverse body preserves arrayOutOfBounds in source order: a missing prefix entry fails before multiplication, a missing output entry fails after the first canonical multiplication, and a missing input entry fails after the local output write. Prefix failure covers arbitrary accumulator words; later cases explicitly require the canonical operands already covered by R250. R306 transfers these body results to the second reverse body by definitional equality. This does not prove caller index invariants or whole batch/source-library correspondence.

Compile revision `04d7d1b635ddb7c9af2ee3e2df3cdb68ae68bb43`; exit 0; wall 0:01.51; child peak RSS 3710172 KiB; swaps 0. All three complete axiom reports use only propext, Classical.choice and Quot.sound. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r313-current-batch-reverse-index-errors/manifest.json).

First remaining proposition: Prove complete reverse-loop termination and its output under explicit local invariants, then derive those invariants and all success/error conditions from the actual batch guard, prefix traversal, total inverse and initialization.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.

Subsequent result: [R311](R311_CURRENT_BATCH_REVERSE_LOOP_EXECUTION.md) proves complete reverse-loop termination/output under the explicit local invariants. The next missing argument is establishing those invariants from the actual forward prefixes, vector allocation and batch initialization, then composing all guards and failures. The R313 evidence records the frontier at its own compilation.
