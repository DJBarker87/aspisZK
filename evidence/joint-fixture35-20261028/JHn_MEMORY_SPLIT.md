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

The second replacement PASSES: 084–089 separate JHn_ByteSHA (exactly three
concrete equations, without a tree class), derive actual body/saved/returned
identities under it, prove that class unconditionally from the separately
checked equations, then compile JHn_ExactReturned.source with NO SHA premise.
Attempt089: exit0,5.386547416s,6762880KiB,swap0,standard root axioms.

Attempt090 (`JHn_TX1`) combines the unconditional byte implication with the
restored conditional candidate and SDK wrapper. It fails during import at
interpreter: exit134,7.239616313s,7272464KiB,swap0,no axioms output. There is
NO checked JHn_TX1.accepted1_saved. The failed source is a draft.

Replacement091: JHn_TX1Frontier retains acceptance and the same returned
candidate/child witness under only JHe_SHARealization. Its assembly lemmas
explicitly take ByteIdentity, whose exact formula is separately proved by
JHn_ExactReturned.source. This is an assembly INTERFACE, not a claim that the
remaining premise was discharged. It passes at7146216KiB. Attempt092 corrects
the witness's prose to say length1768 rather than claiming byte identity and
rechecks that new source. Final checked application of the two environments
is left to the owner's separately approved aggregation step. No cap increase,
module-system workaround, unchanged failed rerun or assumption added to SHA.
