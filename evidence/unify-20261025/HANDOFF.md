# Uni handoff

**S2 OPEN; target not yet established.** Branch `codex/cx-unify-20261025`.
All changes are new Uni_ modules, this task's evidence, and an appended ledger
section. No push, shipped/cfg(kani) edit, session A or sibling-worktree edit,
key cleanup, artifact rebuild, package replay, Rust or Kani run.

## Established

`lean/Uni_Accepted.lean`, theorem
`AspisR1.Uni_Accepted.accepted_pair_unified`, composes ONE accepted pair and
ONE f,s,cuts. It retains every Op5T_Final/Tx2I conclusion, adds Op4P scan and
the entire Tx1Q run/WhenBound conclusion, and installs the union of shape
TX1+TX2, scan, both batch slots, authenticated TX2/finish, and TX1
query/flush/writer plus its prefix helpers. `Uni_Install`, `Uni_Slots` prove
full dictionary commutation and agreement, not assumed compatibility.
`Uni_Cuts` derives the new conclusions from the exact exported cuts.

`Uni_SecondMarks` checks source TX2 resume/batch1/query1/finish on every
successful literal authenticated call, with a successful control fixture.
`Uni_RejectedSecond` proves the empty-proof shape rejection has no suffix
sites and conflicts with the old globally source-faithful SecondMarks.

`Uni_CanonicalPerAttempt.final_soundness` supplies the missing canonical
per-attempt endpoint, returning EXACTLY the existing per-attempt Claims on
lift P with the unchanged repeated/adaptive bound and Q range. It uses the
existing canonical raw join, Physical and StoredCarrierBinding, and derives
the canonical annotated join. `no_global_join` proves why old L155 is false
for any accepting physical source. It is retired, not proved.

## Premises and non-vacuity

See STAGE-B/C.md and premise-audit.json for full before/after statements and
changes to quantification. L164 is discharged for this checked union.
L089/L090's unguarded C fields are replaced throughout the chain by actual
Rust-Ok guarded P source-instance laws. L155 is retired for the canonical
endpoint; its replacement L157 was already P. Targeted-row accounting is
T88/P109/C0 versus T88/P108/C3; this is NOT an exhaustive recount of all
newly imported continuation fields. Every other original ledger row is
unchanged, including historical L156, which the new endpoint does not use.

`source-fixture-audit.json` reuses the exact-default-ELF successful LiteSVM
transfer-13 pair and freshly checks all562 admitted source hashes: all match
this worktree. Stage1/stage2 both succeed at f8c0ec72…. Historical readonly/1
failed and is excluded; readonly/2 is the selected successful evidence.
Uni_Audit also proves consistency of extraction on the exact union. Neither
is a proof that ALL remaining runtime/crypto/log/model premises jointly hold.

Open: faithful SDK child/log reification, raw canonical ordered-log join,
StoredCarrierBinding, selected-map/provenance transport, WhenBound and owner
laws, saved_ten/twelve, native writer adoption, and coherent frozen release
association/replay. The accepted-pair and corrected headline are still
connected conditionally through these explicit obligations. No body/source
refinement gap is reclassified as cryptographic trust.

## Validation and exact scope

10/100 Lean attempts (zero dependency builds); 0/0 Kani. Eight pass;
004 and006 fail only during elaboration, then changed proofs pass005/008.
One initial launcher missing-path preflight launched no Lean; the existing
Tx1Q cached path resolves the unchanged Op4P imports. No launcher repaired,
shared object overwritten, timeout, memory kill, raised limit or unchanged
prover retry. Uni_010 is the one final statement/field/axioms audit of all21
new top theorems: only propext, Classical.choice, Quot.sound. Failed diagnostic
sorryAx output is excluded. No forbidden proof token or limit override in
final sources. Final successful snapshots match all committed Uni_ modules.

Each invocation ran `lake env lean -j1 -M7000 -DElab.async=false` inside its
own MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 systemd scope using
unchanged launchers and the coherent SInt2 cache first. Initial and final
host scope inspection showed only init.scope. Per-attempt JSON/stdout/time
records exact target/command, revision+dirty source hash, direct object and
sidecar fingerprints, exit/wall/RSS/swap/limits and full axioms. No full frozen
closure replay is claimed.

Union target Uni_003: exit0,2.623330939s,peak5212868KiB,swap0,
source anchor7e89e9cb1d plus source hash in receipt.
Final Uni_010: exit0,1.992542262s,peak5224872KiB,swap0,
source anchor752cd94cd8 plus source hashes in receipt.

ELF rebuild trigger did not fire. Inherited, not freshly rebuilt:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Next concrete deliverable: instantiate the source-associated SDK child
reification on this union's SAME accepted f/s and use it to transport actual
ordered logs into L157 and L159. The deployment and100-bit target remains
not established.
