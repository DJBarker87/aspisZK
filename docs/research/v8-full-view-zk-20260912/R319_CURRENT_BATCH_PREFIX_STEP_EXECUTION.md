# R319: actual forward-prefix body execution

`AspisV8R19/R319BatchPrefixStepExecution.lean` compiled successfully. The actual loop body stops exactly when the pinned iterator is exhausted. For every raw active input it equals the original unwrap/multiplication/push chain, retaining all failures and divergence. An empty prefix panics before multiplication; canonical selected input and last-prefix values plus local capacity imply exactly one encoded product is appended and the iterator advances once. The second source loop body equals the first. These are the selected generated bodies under the retained executable Aeneas library model; independent Rust-library correspondence and caller invariants remain open.

Compile revision `b268da1cb6878d9b1ab6c2cab79b0592d04dd0ca`; exit 0; wall 0:01.64; child peak RSS 3709456 KiB; swaps 0. All seven complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r319-current-batch-prefix-step-execution/manifest.json).

First remaining proposition: Prove the complete forward loop prefix recurrence and stopping under these explicit local invariants, then derive the invariants, guard and inverse initialization from the complete source batch. All-word full-loop failures, chain/any, freeze fold/extend and callback chronology remain open.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
