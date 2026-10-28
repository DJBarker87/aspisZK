# Memory failures and replacements

Attempt026 (`JHn_SavedFromTrees`): exit134, Lean memory_exception at interpreter,
4.386791771s, peak7183136KiB, swap0. No axioms output; no theorem credit.
It combined the actual returned-vector identity with all three separately
proved digest equations and the453-tree SHA class environment.

Replacement: isolate the already proved claim's serialization in
JHn_ClaimBytes. Remove the SDK/joint-skeleton import from JHn_BodyIdentity;
compile BodyIdentity, PreparedBody, ActualBody, SavedIdentity and
ReturnedIdentity sequentially (028–032). Those targets pass and reduce the
body-only import environment. No arithmetic is re-proved, no cap changes.

Attempt033 (`JHn_SavedFromTreesSplit`): exit134, memory_exception at interpreter,
4.583312981s, peak7246004KiB, swap0. No axioms output; no theorem credit.
The narrowed environment still cannot combine the453-tree class with the
three numerical byte-digest proofs and body reasoning. Both failed sources
are retained as drafts and receipt snapshots, not active proof roots.

Next structural replacement, prepared while the independent batch cache is
restored: separate the writer's THREE concrete digest equations into the
JHn_ByteSHA class WITHOUT the453-tree class. Discharge those three equations
separately in JHn_ByteSHAProved. The writer implication needs no tree
realization; only batch acceptance does. This keeps desired success/body laws
out of SHA classes. The final acceptance assembly retains only
JHe_SHARealization if it fits. No retry of026 or033 unchanged is authorized.

All jobs retain -M7000, MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64.
The module-system route and a larger cap remain unavailable.
