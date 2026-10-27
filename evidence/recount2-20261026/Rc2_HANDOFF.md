# Rc2 selected composition and mechanical recount

S2 OPEN; target not yet established. Branch codex/cx-recount2-20261026.

The ONE selected root is `AspisR1.Rc2_Top.deployed` in lean/Rc2_Top.lean.
It applies T2R_Top at Rc2_Install.select, proving dictionary compatibility and
sharing the same f/s/outer/pre/middle/fs/ss/run/tx2 and semantic Claims witnesses.
It adds NP6 initial/pending/parsed Claims contents, PoolT accepted copy and full
frame, CPS computed source-bank events, CPP atomic oracle-log preservation,
CPR rollback and guarded bank-model effect/protection. No frozen3 or runtime
persistence law is selected. The original version's extra guarded history
corollary was removed in 9460fbd547; standalone Rc2_History is excluded development.
CPS_SourceTop.correlated's source-event component is composed directly through
CPS_BankRecorder.events; its physical correlated-history conclusion is not
asserted absent the explicitly excluded runtime law and associations.

Rc2_Install replaces the free Claims std dictionary with NP6's checked selected
safe instance; it does not assume equality with arbitrary c.std. NP6's retained
full source-helper certificate supplies the Claims-local native interpretation,
with existing allocator/runtime/extraction trust retained. Whole library/native
frame and frozen artifact association remain. This is a selected installation,
not a proof for all arbitrary dictionaries; game/metric/query constants unchanged.

## Recount (authoritative final data)

Rc2_recount.py renders the complete kernel statement/field audit by the
Ledger_003–005/Cons method. Rc2_022 prints the full top and nested fields afresh;
Rc2_field_catalog.json and Rc2_premises.json retain exact evidence and decisions.
The new section at the END of design/PREMISE-LEDGER-20261025.md is reproduced in
Rc2_LEDGER.md. No prior section is changed.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
| Actual application conditions |82|171|0|23|145|85|
| Non-alias deployment only |6|13|0|12|1|6|
| Deployment aliases |0|5|0|4|1|0|
| Deduplicated actual + non-alias deployment |88|184|0|35|146|91|

Actual conditions include conditional conclusion guards, not just root binders.
All T items are external; actual P ownership is lead23/sessionA145/external3.
Inherited security conclusion slice alone is 82T+166P. Five newly inventoried
CPR guards only gate the added bank-model results: installed key equality,
program owner, nonempty initialized data, exact tag82, positive lamports.

Diff against Cons: remove L085/L086/L087 (concrete frozen parameters),
L122/L123/L124/L126 (same-reader observations), N116 (selected parser), and
L177 (selected Claims source-helper boundary). Add Rc2_P001–005 above.
L174 was already absent in Cons; NP6 strengthens its output, no double credit.
L179 retains the broader frame obligation with its Claims-local part derived.
All 281 Cons retained rows plus five new guards have a row-level diff.

Every remaining P row has owner, scope, exact blocker and owner-route tags:
a=frozen3 candidate L157/L159 route (also order/transport aliases);
b=runtime-law adoption plus physical game clarification, L094–L096/L180;
c=session A plus explicitly identified lead source/model/binding consumers.
Tags do not claim that adoption alone proves a row. A different proof could
replace an owner route. 21 deduplicated lead P rows have none of these tags:
11 actual conditions and10 non-alias deployment items. This includes event
restrictions/carrier laws, not21 independent new security gaps. Global release
use still depends on all source cones; final trust/artifact work itself can
proceed independently of the pending decisions.

## Validation and reuse

22/60 Lean attempts, 0 dependency builds, 0/0 Kani. Nine excluded development
failures:002/005/007/008/009/011/014/016/021. No wall timeout, memory kill,
cap/heartbeat increase or unchanged failed-source/dependency replay.

- Final top Rc2_019: exit0,2.165615717s,5328524KiB peak RSS,swap0.
- Full final audit Rc2_022: exit0,2.262392340s,5303300KiB peak RSS,swap0.
- All six selected theorem audits exactly [propext, Classical.choice, Quot.sound].

Rc2_validation.json records exact targets, argv, full resolved revisions,
source/dependency/tool hashes, limits, wall/RSS/swap, errors and printed axioms.
It checks all22 receipts/snapshots, source/dependency non-repetition, selected
own dependency consistency, every current source's passing snapshot, unchanged
inherited source closure, NP6 source-certificate pins, row totals/owners/tags,
reproducible rendering and byte-for-byte preservation of all prior ledger text.
Rc2_source_manifest.json pins selected and excluded own sources and the unchanged
transitive source closure. Reused coherent SInt2 objects plus accepted
T2R/Cons/NP6/PoolT/CPS/CPP/CPR caches. No fresh full frozen closure replay.

Every actual compile used the unchanged S2W launchers, -j1 -M7000,
-DElab.async=false; scopes MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64.
Existing S2X reservation barrier ran before each launch. One own scope at a
time; all reservations allowed, no barrier retry. No infrastructure repair.

No shipped/cfg(kani) change, so ELF rebuild trigger did not fire. Inherited
pins, not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No foreign module, session A worktree/candidate, key/wallet or release scope
changed. No push. Next deliverables: owner routes a/b/c, source/model and saved
Context/Vec association, concrete primitives, source/artifact and release audit.
