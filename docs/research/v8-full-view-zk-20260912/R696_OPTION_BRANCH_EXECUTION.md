# R696 Option branch execution fragment

The extracted `Option::branch` body is now checked directly in Lean for both variants and for an arbitrary `Option T`. This proves only that captured branch function’s local result behavior.

The canonical source is [R696OptionTryExecution.lean](lean/AspisV8R19/R696OptionTryExecution.lean), SHA-256 `85b9b06faa6788a26784ae0a9846644629b0f9f615e3ab84410fd7833bd6c0ee`. Its generated branch declaration was copied byte-for-byte from the captured `Funs.lean` lines 38–50. The full generated source, including the adjacent `from_residual` body, original LLBC, capture/translation pins and logs, extracted source slice, every Lean attempt, and full axiom output are archived in [r696-option-branch-execution](evidence/r696-option-branch-execution/).

The focused Lean 4.32.0 check used `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. It exited 0 in 0.99 s with peak Lean RSS 2,560,796 KiB and swap 0. All three complete axiom reports say no axioms: `branch_none`, `branch_some`, and `branch_exact`.

The earlier captured `Option::from_residual` body is preserved with its `read_discriminant` call and `massert` guard, but it is not proved here. The pinned official Aeneas sources have no `Option` discriminant instance. `Option::unwrap_or_else` and the other standard-library template operations also remain opaque. These gaps leave the actual owned fold, callback chronology, privacy, and soundness obligations open. The first remaining proposition for this leaf is exact execution of the preserved `from_residual` body using a justified `Option<Infallible>` discriminant model. No custom Option tag or discriminant assumption is introduced.

Exact source revision: `a2f0cb4ee9e7afe492b55c8424e31fabbcd12f23`; target `AspisV8R19/R696OptionTryExecution.lean`; final run `1791125417980625000`. Native compiler/caller adequacy is not established by this local generated-code theorem. Verifier/security parameters and CU999790/999532 remain unchanged.
