# R311: complete selected reverse-loop execution under local invariants

`AspisV8R19/R311BatchReverseLoopExecution.lean` compiled successfully. The unchanged generated reverse loop terminates and returns exactly the finite mathematical reverse recurrence against the pinned executable Aeneas library, for every representable range with start=1/end=n+1, the explicit canonical selected-read equations, and n below output length. Induction unfolds the actual runtime partial-fixpoint equation; termination is proved, not assumed. The model-only Nat-indexed output update is proved equal to actual Vec.set at the yielded word index. The second reverse loop is definitionally equal to the first. Zero field operands are allowed; the batch inverse/zero guard and all caller premises remain unproved here.

Compile revision `78d28cdea0f1ac2fd332f92026071c654b9b3a52`; exit 0; wall 0:01.75; child peak RSS 3724832 KiB; swaps 0. All five complete axiom reports use only propext, Classical.choice and/or Quot.sound. No sorryAx or additional execution axiom is used. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r311-current-batch-reverse-loop-execution/manifest.json).

First remaining proposition: Derive all reverse-loop read equations and range/output bounds from actual forward prefix loops, vector allocation and batch initialization, then compose the guarded total inverse and both outputs with complete batch success/error behavior. Independently close standard-library Rust correspondence and full callback chronology.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
