# PoolU handoff — native composition not established

Branch codex/cx-pool-write3-20261026, base83b9c6fbd1. Local stage commits only;
no push. **Target not yet established; zero global S2 premises removed.**
No concrete accepted attacker-chosen checkpoint write found.

## Proved versus missing

`lean/PoolU_Step.lean` proves source-ordered success inversion and exact error,
interpreter-failure and divergence prefix preservation. `PoolU_CopyTail.accepted`
derives full192/384-image copy outputs (for arbitrary byte lists, not assuming
those sizes), physical-key other-account frames and all metadata frames from
ONE successful reference prelude and its actual returned images/post-prefix
store. It retains any earlier System effects by starting the copy at that
post-prefix store. `rejected_prefix` preserves the exact source error/state.
These are mathematical/reference composition results, NOT native P1 refinement.

The requested `PoolU_Write.accepted_p1_writes_copy` is neither defined nor proved.
`PoolU_MISSING_LEAVES.md` specifies the missing original planner/decoder/PDA and
caller decomposition, cleanup/error/effect and canonical-action coupling facts,
with precise production spans, inputs and conclusions. `PoolU_LEAF_INVENTORY.json`
pins all70 historical PoolW/PoolV/Hir Kani receipts and distinguishes failed
original-planner gates from passing projected chronology/loop/assembly gates.
No Kani leaf fact was invented or silently assumed. The whole native prelude
remains uninstantiated; its explicit function parameter is not premise removal.

P1 writes the planner's ASC8 after optional System CPI; it has no verifier CPI
and does not write verifier-returned CP. Existing Hist/Hiq/Hir CP native-child/
copy results remain separate. The missing-fact report gives the exact interface
needed by phase2 and the runtime-history worker. Existing runtime/Solana/CPI and
SDK/copy boundaries are retained; no new runtime item/trust adopted. No security
contract, metric, failure event or release target changed.

## Validation and budget

Lean4/100 submissions:001,003,004 pass;002 syntax error from reserved identifier
`prefix`, fixed by changed source003. No timeout/memory kill, unchanged rerun,
package/manifest replay, Kani/Rust/extraction/SBF run. Kani0/0. The Lean allowance
is NOT exhausted. This is the requested precise missing-leaf report, not a claim
that budget exhaustion or theorem completion occurred.

Every invocation ran in its own existing-launcher host scope, high6G/max8G/
swap0/tasks64, -j1 -M7000 -DElab.async=false. Reused coherent SInt2/Hiq/PoolW
objects, unchanged. Per-attempt receipts record exact command/target, source
revision/hash/snapshot, selected object/tool hashes, exit/wall/RSS/swap, caps and
full axiom lines. Final statement/axioms audit004: exit0,1.535175203s,
peak4333144KiB,swap0; revision c64dcea689 with dirty audit source, exact SHA in
receipt. All six new theorems use only standard axioms; no sorry/axiom/admit/
native_decide or new heartbeat/depth options. Failed source/log preserved.

`PoolU_validate.py` passes current source-to-receipt mapping, all snapshots,
standard axioms, caps, swap0, leaf receipt hashes, frozen source and all157
inherited compiler inputs, allowed-prefix diff and binary exclusion checks.
Final host source/object hashes and scope inventory: PoolU_HOST_FINAL.log.
Only PoolU_ modules/evidence changed; no launcher/tool/monitor infrastructure
was created or modified. No other worker/worktree/candidate or keys/funds touched.

No shipped file or cfg(kani) module changed; no ELF rebuild trigger. Inherited,
NOT rebuilt/deployed-attested pins:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
