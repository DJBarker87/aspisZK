# R306: bounded selected reverse-body execution

`AspisV8R19/R306BatchReverseStepExecution.lean` compiled successfully. Against the pinned executable Aeneas library, the generated body stops exactly when the reverse range is exhausted. An active step reads the explicitly specified canonical prefix and input words, writes the prefix-times-inverse output at the yielded index, advances the iterator, and updates the inverse accumulator. The two generated bodies are definitionally identical after renaming. Selected-read equations and the output index bound are explicit local premises; this does not establish them for the batch caller, prove the batch zero guard, or prove full callback chronology.

Compile revision `04d7d1b635ddb7c9af2ee3e2df3cdb68ae68bb43`; exit 0; wall 0:01.70; child peak RSS 3724492 KiB; swaps 0. All complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native evaluation or new execution assumptions. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r306-current-batch-reverse-step-execution/manifest.json).

First remaining proposition: Establish the complete reverse-loop invariant and termination from actual prefix vectors and batch initialization, preserving index errors and stopping; close independent standard-library source correspondence and the full batch guard/prefix/inverse execution.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
