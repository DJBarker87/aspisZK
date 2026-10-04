# R708: cleared circle substitution polynomial

Exact target: `AspisV8R19/R708ClearedCircleSubstitution.lean`. Source revision `16aca98195bde6dd82aa6ea453fc29da0cc449c7`, SHA256 `e6ed621a0a1eeca7b489ce994874fe62631bd659f12759930615e34bd9ca3f83`. Final focused run `1791128754841068000` exited 0 in 0:01.55; Lean-child RSS 3260432 KiB, swap 0. Pinned Lean used `-j1 -M4500` under MemoryHigh 5G, MemoryMax 7G, swap disabled, TasksMax 128.

For a nonzero polynomial `P`, the proof defines the symbolic cleared polynomial and proves its coefficient at degree `2*P.natDegree` is `P.leadingCoeff * (-1)^P.natDegree`, hence the cleared polynomial is nonzero. The proof isolates the exceptional index `D` in the finite sum; every index below `D` is eliminated through a symbolic degree bound. No concrete degree or finite-field recurrence is evaluated.

This establishes only highest-coefficient/nonzero algebra. It does not establish the evaluation identity at a nonzero circle parameter, an actual circle parameter law, native execution, an application to R707, multivariate nonvanishing, or any security claim.

All changed attempts are retained, including the initial broad `Mathlib` import that exceeded Lean's 4.5G interpreter threshold (exit 134, RSS 5,941,080 KiB) and the narrow-import API drafts. The final three axiom reports are standard `propext`, `Classical.choice`, and `Quot.sound` only. No unchanged successful target was rerun.
