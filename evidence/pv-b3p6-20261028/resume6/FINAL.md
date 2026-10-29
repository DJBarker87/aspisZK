# D405 resume6 — V244 still open; round suspended at budget exhaustion

Worktree `/Users/dominic/ZK/.worktrees/pv-b3p6`; branch
`codex/pv-b3p6-20261028`; entry `897c2b28a6265d94da66bf455792a5f73cc66bdc`.
[Commits](COMMIT-LOG.txt). **100/100 Lean attempts**, IDs60800–60899 exclusively;
81 passing targets and19 rejected attempts, all retained. Four admission
refusals were uncharged and retried after the full cooldown. **Zero native
Rust scopes, zero Kani.** V241/V245 were not started.

No ledger-row or endpoint premise was removed, added, weakened or moved into T.
V228/V229/V243 retain their accepted status. **Target not established.**

The checked `PV_B3P_Success227.public_nonvacuity` supplies an unconditional
`.ok (.Ok ())` witness for the **validator fragment**. Its public family uses
the first20 rows of the empty-frontier table symbolically; no root words are
computed. `PV_B3P_Success227.preparation_success` then establishes successful
validation,84-cell selection, three C1 rows, ten mask cells and selector
construction for arbitrary claims and point in that public family.

Other checked supporting laws cover bounded expansion/interval/carry/reverse
loops, both packers, prepared arithmetic/accumulation, equality, global sums,
and semantic initialization/absorption. The global-sum recursion-limit failures
were replaced by shallow named theorem applications; no cap or recursion limit
was raised. [Per-theorem classifications](theorem-classification.json) label
all97 new statements' Rust interpretations as **reclassification within existing
Charon/Aeneas tool trust**. These are not a full native binding or full reference
nonvacuity. Generation checks pass; no whole reference reduction, decision-
procedure proof of nonvacuity, XR import, new axiom or new max option was used.

Runjoin's `R1Z.PV_RunJoin_OracleBridge38.selected_callback` hypothesis is
**not discharged**. There is no replacement theorem to consume. The exact
unchanged hypothesis and next required functions are in [residuals](RESIDUALS.md):
finish `composition_parts` success and the full reference/installed-callback
`.ok (.Ok value)` witness, then(b) exhaustive source binding,(c) remaining D188
and direct accumulator matrix comparison,(d) slice caller/pre-inline std cone.
Old native64/36 observations are reused only as finite validation.

|Target|Exit|Wall s|Peak RSS KiB|Swap|
|---|---:|---:|---:|---:|
|60897 PV_B3P_Resume6Combined|0|1.632|2609008|0|
|60898 PV_B3P_Resume6Axioms|0|1.197|2598152|0|
|60899 PV_B3P_Resume6Focused|0|1.415|2591744|0|

All three targets' exact Lean source revision is
`69ac50af4cd90844875baa67ba319126e5cd060a`; Rust source/configuration freeze
and deployed-feature evidence are retained unchanged from resume5. No Rust
source was edited, so no release ELF was rebuilt. [All100 receipts](receipt-index.json)
retain exact commands, source/dependency hashes, revisions, resource limits and
full multiline `#print axioms` output. The97-theorem audit accepts only propext,
Classical.choice and Quot.sound. All100 source snapshots match and5,673 external
objects were verified before the first compile. Peak process RSS was6,605,692KiB;
all swaps0, every scope6G/8G/swap0/TasksMax64, Lean-M7000.

Compiler-cohort semantics remain at the owner's D381/D386 boundary: `ctpop`,
`core::fmt::{vtable}`, `{vtable_drop_shim}`, and the `write_str`, `write_char`,
`write_fmt` `{vtable_method}` glue. [Exact names and intrinsic calls](compiler-boundary.json)
include abort, add_with_overflow, cttz, is_val_statically_known, unchecked_add,
unlikely, wrapping_add and wrapping_sub. None enter T. T remains exactly
entropy_law/entropy_kernel/observation. V165/V167, E1/E2, real RunJoin, client
proof-account routing and L1/L2/L3 remain substantive; simulator/observer unchanged.

Only this worktree and its private host directory changed. No merge/push,
shared-source writes or key deletion. [Object hashes](resume6-object-manifest.json)
and [cache hygiene](cleanup-resume6.json) retain sources and receipts while
removing only rebuildable private proof objects after the final dependent replay.
