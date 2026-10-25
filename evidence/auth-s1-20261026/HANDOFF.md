# AuS1 handoff — authentication input removed in joint extension

Branch `codex/cx-auth-s1-20261026`. No push. Shipped source unchanged.
The release security target remains **not established**.

## Checked deliverable

`lean/AuS1_Accepted.lean`,
`AspisR1.AuS1_Accepted.accepted_pair_unified` (073; final audit078), extends
SdkD_Accepted with one shared TX1 run and `AuS1_Finish.Outcome`.
Its NEW finish continuation needs neither `authenticated_S1` nor an arbitrary
recovered-map input. It returns the existing collision event OR the original
three finish conclusions. The original SdkD Outcome is retained alongside it.
All22 authentication equalities and the original folded-root frame read are
also explicit outputs. The same f,s,cuts, prepared return, root range/copy,
writer call and actual TX2 source cut are used throughout.

This is deterministic authentication-input discharge UP TO the existing
collision alternative, not a deployed probability/security theorem. GExp must
still identify the actual containing source/adversary experiment and its
uniform whole-experiment Q. No global experiment-equality premise was smuggled
into this top, and no numerical global-security closure is claimed.

## Before / after and ledger delta

See AuS1_STAGE4.md for full quantifier/carrier/failure-event audit and ledger
delta, and AuS1_before-statement.lean.txt / AuS1_after-statement.lean.txt for
exact statements. The stronger continuation retains named SessionAPrepare and
all other arithmetic/parser/matching/writer/runtime/Session A premises.
No trust/crypto assumption added. Its collision alternative replaces the
former authentication input. L157/L159 global experiment rows remain OPEN.
The old theorem is unchanged; removal credit applies to the stronger AuS1 path.

The dictionary now specializes only previously free folded-root slots to the
literal source offsets/unwrap. AuS1_Install.dictionary proves compatibility.
A new DATA parameter `prior : Program Bytes State Unit` permits the actual
preceding oracle history; no Prop field asserts its consistency or acceptance.
Its consistency follows from oracle-program evaluation. GExp supplies the real
history in its pre-H experiment; an arbitrary accepted proof alone is not
claimed to define that global probability experiment.

## Proof path

- AuS1_Prepare.associated derives COMPLETE explicit preparation-tree syscall
  association, including semantic/original/scalar/query children, for partial
  native syscalls; no success/totality law is inserted.
- AuS1_PrepareRead.frame derives row30's original commitment read from actual
  prepare/sourceView, physical range7751..7783, literal Vec copies and source
  scalar absorption. Its offset38 target is committedRoot parsed2.
- AuS1_Context + AuS1_OnRun derive source-prefix recovery or collision from
  both actual source batches' six canonical checks on the SAME chosen run.
  SdkD_SecondModel uses the full writer/reader raw-root/all22-query transport.
- AuS1_Map.occurrences gives packed agreement and repeated-parent consistency,
  including positions on opposite sides of split10. AuS1_Stability proves later
  ordered calls cannot alter the original commitment-prefix map.
- AuS1_Finish.strengthen consumes that DERIVED recovery alternative in Tx2N's
  existing arithmetic result; no authentication callback enters the joint top.

AuS1_Bound names the unchanged existing bound term
`6*(Q+1040)^2/2^256`. ALL1040 replay queries are charged once. Its generic bound
law still requires the source experiment's uniform Q, owned by GExp. The top's
collision uses actual firstReads of its constructed prior+prepare trace; do
not silently substitute a global Q without the containing-experiment proof.
No claim is made that preparation-only logs cover adaptive prover history.

## Success conditioning and non-vacuity

Association, source erasure and observation lemmas cover all outcomes.
Frame/ROM/recovery claims require actual source success and replay success;
those are derived on accepted cuts. The final finish statements retain the
existing other-cone gates and named SessionAPrepare. No unconditional source
success, total syscall law or impossible full rejected-suffix layout is used.

The introduced source laws are proved, not assumed records. Prior is arbitrary
program data (done() is admissible). Joint kernel inhabitation of ALL remaining
runtime/model/crypto hypotheses is NOT established. Reused exact-default-ELF
successful two-TX LiteSVM fixture is retained; a fresh static comparison found
zero mismatches across its562 admitted source hashes. See
AuS1_nonvacuity-source-audit.json. This is not a fresh runtime execution or a
full joint-premise fixture. Existing SdkD_Nonvacuity is re-audited in078.

## Validation / resource / freeze

Budget used: **78/100 Lean, 0/20 Kani**. Stopped after the assigned input was
removed from the checked stronger joint branch and the final axioms audit
passed; no budget-exhaustion or shipped counterexample claim.
Every CURRENT AuS1 module has a matching exit0 source snapshot. See
AuS1_final-audit.json for all attempts, exact metrics and final source hashes;
AuS1_host-object-manifest.json pins current source/objects/sidecars by hash and
size only. Failed development attempts are retained and excluded. Default
heartbeat failures009/012/055 were fixed by source/proof isolation; no raised
limit, unchanged timeout rerun, memory kill, package or full manifest replay.

All Lean invocations used the existing S2W launchers in the coherent SInt2 host
workspace, one module, -j1 -M7000, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/
TasksMax64. Source revision/dirty-source hash, selected import-object hashes,
exact command/target, exit, wall, RSS, swap and full axioms are in each receipt.
Final top073: exit0, 3.313469615s, peak5264096KiB, swap0, revision anchor
7e36641a9b plus exact dirty source SHA. Final audit078: exit0, 2.106172394s,
peak5204124KiB, swap0, source revision bc30da2760 plus exact audit source hash.
All checked new theorem axioms are subsets of propext/Classical.choice/
Quot.sound; private bind helper has none. Final audit covers every new theorem.
076/077 were excluded audit-option/name-development failures, not theorem
failures. No build/launcher/monitor infrastructure was modified.

Only own prefix modules/receipts changed; no session A live worktree or other
worker prefix was touched. No Rust, Kani, SBF, keys or funds operations.
No shipped/cfg(kani) change, so conditional ELF rebuild trigger did not fire.
Inherited pins, NOT freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Next concrete integration: GExp selects the actual prior oracle program,
associates complete ordered source/adversary history and rejected prefixes,
charges its uniform Q, and transports the collision alternative to the global
loss bound. Full frozen source-to-ELF and release replay remain lead work.
