# Runjoin65 session-1 handoff — budget exhausted

Exact worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`; branch
`codex/pv-runjoin-20261026`. Sole writer authorization was supplied by the user.
No push. Recovery receipts and evidence are committed; see REPORT.md.

ALL IDs76000–76099 spent, audits76097–76099 included. 100 charged Lean attempts,
66 accepted,34 rejected,0 Kani,7 historical uncharged refusals. No remaining ID
or attempt in this block. Never reuse an ID. Final host reconciliation verifies
100 original results,300 matching files,no active pv64 scope/cgroup,no other-job
ID hits. No unresolved submitted scope remains to collect.

Checked additions: NativeCommitmentQuery64.complete produces the word/lane and
stored-salt bounds from successful native salted Commitment.build;
NativeSaltContext64.complete proves contextual folded salts have length262144;
FoldedLeafWord64.complete derives folded-word size from successful inner leaf
construction at65535. FoldedLeafLimits64 passed76096. Three axioms audits passed
76097–76099 with only propext,Classical.choice,Quot.sound.

NEXT, only after a fresh ID allocation: compile the committed UNCHECKED
PV_RunJoin_FoldedWordSize64.lean (the only round64 source without an accepted
matching receipt). It symbolically visits outer folded_leaves at65535 and
consumes FoldedLeafWord64. Stop and change the source on any proof failure.
Then use FinishTrace.source plus FinishFrame63 to derive contextual folded-word
size; recover both backend commitments' successful salted constructor
provenance, consuming NativeCommitmentQuery64; join with NativeQueryPrimitive64
for full QueryAppend. FinishContext still requires its full field association.

Nonempty P at opsNative remains unproved: Sequential64 and SequentialSource64
are generic scheduling tools only; bind actual NativeControl.run and prove the
sequential op227/op257 residual success conditions on reached inputs plus the
allocator world. No separate model witness is needed under(v').

CommonSample,BackendInput,FinishContext,QueryAppend,NodeAppend remain open.
No ledger row or endpoint premise removed,added or changed. Three TrustItems,
observer,simulator and release pins retained. Target not yet established.
No implementation/Rust/SBF/Kani/key/funds/push operation ran. One scope,
6G/8G/swap0/TasksMax64,Lean-M7000,admission and failed-source guards retained.
The coherent pinned host cache remains available for dependent continuation;
receipts are not cache and must be retained.
