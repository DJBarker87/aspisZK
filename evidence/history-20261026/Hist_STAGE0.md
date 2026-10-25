# History stage 0

Branch codex/cx-history-20261026, initial revision b57e886291.
Budget: 100 Lean attempts including dependencies, 30 Kani runs. Used 0/0.
No shipped source changes, keys, other worktrees or other prefixes touched.

Read the repository security/proof discipline, common/local rules, S2 handoff,
plan/diagnosis and route-B addendum at their tracked research-prefix locations;
S2LeadInterface; premise ledger including Uni update; RowOrder, SInt2, SdkD
and WAdm handoffs. The latter two do not discharge the history/P2Prime rows.

The actual owned source stage1_owned requires zero checkpoint bytes, then writes
only verifier account2. stage2 snapshots account6, requires it readonly and
verifier-owned, reconstructs public bytes, and performs no account-data write.
The outer release guard rejects lifecycle4/5/6 before dispatch. Pool retained
forest checkpoints are separate immutable PDA records (pair_forest.rs planner
and zeroed fresh-PDA gate). ASQ8 request320, ASF8 public1880 and verifier CP1768
must never be identified. Proof/public input buffers may have arbitrary owners;
thus protected verifier-checkpoint history alone cannot imply their retention.
The fallback is explicit collision-event byte binding, with a charged uniform
query bound for the entire containing program; no SHA injectivity hypothesis.

Baseline statement: RowOrder_AcceptedPairHistory.accepted_pair_history retains
CheckpointVersionBinding.savedAtCommit/loadedAtEntry/noInterveningWrite and
P2Prime on the same cuts. No source/program refinement is discharged by this
source inspection. Target rows L094-L098 and L180 remain open at this stage.
No security metric, failure event or accepted-run quantifier has been changed.

Hist_source-pins.json records actual source hashes and comparison to the retained
exact-default-ELF successful pair fixture; no fresh runtime or ELF rebuild claimed.
Next: focused extraction guard lemmas and collision-or-identity on the existing
consistent bounded oracle log. Reuse coherent SInt2 objects without overwrites.
