"""Finalize only from reviewed terminal evidence; no proof or native job launches."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
v=json.loads((E/'NFV_VALIDATION.json').read_text());assert v['counts']==dict(kani=80,lean=50,extract=1)
audit=json.loads((E/'NFV_AUDIT.json').read_text());assert audit['root_count']==103 and audit['own_module_unresolved']==0 and audit['inherited_unresolved']==650
c=json.loads((E/'NFV_C_LIFTS.json').read_text());assert len(c['rows'])==20
b=json.loads((E/'NFV_REQUEST_WINDOWS.json').read_text());assert len(b['rows'])==13
assert all(p['matches'] for p in json.loads((E/'NFV_ELF_PINS.json').read_text())['pins'])
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
common='''Frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No shipped files
edited; cfg(kani) patches only in the scratch tree. All three ELF hashes match
(default f8c0ec72...,devnet63ad3e9c...,Pool121f3e29...). This is a hash recheck,
not a rebuild. Every native run passed frozen graph/deployed-feature checks
before launch and unchanged Cargo.lock after; offline,opt3, exact KMX patch.
Every scope had MemoryHigh6G/MemoryMax8G/SwapMax0/TasksMax64; swap0. Source
revision/hash, exact command, exit, wall time, peak RSS and axioms are retained
per attempt. Failed proof-development attempts and compile failures are excluded.
No timeout was rerun unchanged, no caps raised, no writable-static or Option<fn>
credit used, no SHA body or field multiplication executed in Kani.
'''
(E/'NFV_HANDOFF.md').write_text('''# NFV final handoff

Overall production association OPEN. No new composed NDT row or headline
closure. Branch codex/cx-pool-retdata3-20261104; committed stages, never pushed.
Budget EXHAUSTED:80/80 Kani,50/50 Lean,1/1 extraction. E001 reached an Aeneas
abstraction-merge Unreachable; no bridge credit and no rerun.

A: AccountMeta and AccountInfo CLOSED-BY-RECLASSIFICATION under(af)(3).
NFV_AF_CERTIFICATE.json records24 full per-index and8 stricter byte timeouts,
with the adopted constructor/flags/length/appended-element native certificate.
Bound205=6*34+1 is incomplete for the SAME AccountInfo copy;337=7*48+1 is used.
Retained std/allocator P6/D188 realization is RECLASSIFICATION, never removal.
No native copied-prefix PASS and no shipped bug claimed.

B: request-encoder source cut has five positive windows and five failing byte
controls, plus argument/error/guard controls (K058/K059,K070..080). Full typed
payment replies and all error paths remain. Symbolic envelope, indexes,
comparison, five-window coverage and emitted-caller erasure are proved. K067
planner with K068/K069 controls remains a restricted EMPTY account-data probe.
The full admitted account/borrow/layout/marker/request prefix remains OPEN.

C: all nine SAME-object observations lifted at cap=len792 into7meta/320request/
8info context (K038..055), with matched failures and two borrowed-context
identity controls(K056/K057). K030/K034/K043 retained; K051 repr(C) EXCLUDED.
K061 helper source-exact one-call cut and K062..065 byte/error/place/live-
allocation controls pass; emitted helper erasure/domain B003 standard. These
post-admission cuts use(y) semantic transport as P6/D188 RECLASSIFICATION.
Actual input account-data/roles/borrow admission must still be supplied by B.

D: NFV_PoolReturnData.lean imports/provides the audited prerequisites, but
intentionally asserts no NFV_PoolReturnData.association while B is open. The
existing NFR model join retains the approved nonempty RuntimeReturnData row
(792 here), not an arbitrary empty-return equality. No new runtime trust row.

Audit:103 roots(34 NFV+69 inherited), raw authoritative standard axioms;
B046 same compiled driver8 fixtures pass. B050 exits1 solely for the exact
inherited650 references in15 modules, all listed and NOT waived. All10 NFV
proof modules have ZERO unresolved references. No full release replay claimed.

'''+common+'''
Receipts:NFV_ATTEMPTS.jsonl, NFV_AUDIT.json, NFV_VALIDATION.json,
NFV_AF_CERTIFICATE.json, NFV_C_LIFTS.json, NFV_REQUEST_WINDOWS.json.
Own exports/hashes:NFV_EXPORTS.json, under codex-cx-pool-retdata3-cache-20261104/
NFV_final_objects_20261104 and NFV_audit_native_20261104. Use these objects
first, then the pinned imported NFR/NFO/NFJ/NFD/coherent roots. Imported hashes
are in NFV_HOST_PINS.json; Aeneas library pins are in attempt fingerprints.
Own cache is retained. Only own rebuildable outputs were removed.
''')
(E/'NFV_REMAINING.md').write_text('''# Remaining native obligations

A: no further account-copy proof is claimed or required by this disposition;
account associations are CLOSED-BY-RECLASSIFICATION(af)(3), with std/allocator
realization retained. Actual caller-state association belongs to B.

B OPEN, requires NEW Kani native caller/domain certificates:
1. Exact frozen process prefix through request/master/checkpoint/lane decode,
   account/layout/payer/system checks, marker planning/creation and custody
   branch. Log all touched-account/buffer pre-states, full child Results and
   mutations with their exact modifies sets and SAME source arguments.
2. Derive the SAME decoded request/public and each payment-child PacketDomain,
   selected registry/program and all seven meta keys from the actual admitted
   accounts. The restricted planner's empty-data fixtures cannot provide this.
3. Associate verifier pool_route::admitted on the far side of THAT CPI with
   its exact request/account windows. Actual order is Pool admission -> CPI ->
   verifier admission; there is no reversed Pool call path.

C: the cap=len792 read/settlement source cuts and one-call helper now have
controlled native/model association under(y), with K051 excluded. Remaining
production-helper transport: instantiate these cuts in the SAME actual admitted
account-data/borrow context and prove all callee PacketDomains in the outer
caller. This is B, needs native evidence, and is not repaired by a model-only
value equality. No account-write/custody/marker settlement certificate follows.

D OPEN until B instantiates the native facts and existing NFR_ModelJoin on the
SAME production execution. No premise wrapper named SameExecution or bundled
output-equality assumption was introduced. No NFV_PoolReturnData.association
or new composed NDT row is claimed. No independent Lean-only copy/frame/
comparison/envelope obligation remains;50 Lean and1 extraction are exhausted.
Each remaining proof needs Kani caller/domain evidence and its coupled model
interpretation; it cannot be discharged by rerunning these model lemmas.

Audit:650 inherited unresolved references remain listed, not waived. New10
modules have zero. A coherent full release replay remains outside this result.
The joint reachable two-transaction non-vacuity witness is NOT this deliverable.
It still needs actual selected accounts/program, admitted account data/marker/
custody state, SAME instruction with no intervening CPI invalidating return
data, successful validation/lane/settlement, and the retained writer/reader
account state on RPx_Deployed.deployed. Local consistency is not that witness.
''')
(E/'NFV_CONE_DELTA.md').write_text('''# S2 / S6 / S10 cone delta

New composed NDT CLOSED rows:0. Headline RPx_Deployed.deployed remains unchanged;
L154 statement parameter, D188 narrowed. Coherent digest/error slots are op43/
op44. No overall S2/S6/S10 join obligation is promoted to CLOSED.

S2 sub-obligations: model account order/flags and adopted(af)(3) retained std
association are settled; five-window request source-cut observations and their
emitted model interpretation are now controlled. Full production admission,
SAME decoder/caller/registry/layout/marker account-domain transport stays OPEN.

S6 sub-obligations: nine SAME-object read/settlement observations now hold in
7meta/320request/8info context, cap=len792; helper byte/error/place/allocation
cut is controlled and erased to the emitted helper. NFR_ModelJoin derives the
encoder domain from the SAME original valid statement. Production caller
instantiation is still OPEN under B; K051 repr(C) diagnostic is excluded.

S10: no actual account-write, custody, marker, writer/reader or persistence
join is discharged. Lane-image/result-byte preparation does not establish a
reachable successful settlement. Joint two-transaction non-vacuity still needs
the concrete admitted context, SAME instruction/return-data interval, successful
continuation and retained account states. That witness is not this deliverable.

RuntimeReturnData remains the approved NONEMPTY1..1024 row(792 here), the sole
runtime law in the existing return-data model join. Native-contract semantic
transport and std/allocator realization remain P6/D188 RECLASSIFICATION,
never removal; no runtime or cryptographic premise added. Privacy, two-
transaction design and100-bit PER-ATTEMPT soundness are unchanged and out of
scope. Budget80K/50Lean/1extraction exhausted. Own raw roots standard;650 inherited
references remain visible, no waiver and no full release claim.
''')
audit.update(budget=dict(limits=dict(kani=80,lean=50,extract=1),used=v['counts'],remaining=dict(kani=0,lean=0,extract=0)),native_members=dict(A='CLOSED-BY-RECLASSIFICATION af3',B='OPEN production prefix; controlled request-encoder source cut',C='controlled post-admission cut; production caller instantiation OPEN in B',D='OPEN on B'),composed_NDT_rows_added=0,source_revision_before_final_commit=rev,formal_release=False)
(E/'NFV_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
(E/'NFV_PREFIX.md').write_text("""# Production prefix / admission transport

Overall B OPEN. The frozen production call order is Pool account admission,
then pair_forest_dispatch CPI, then verifier pool_route::admitted. Verifier
admission is not an earlier Pool call and cannot supply Pool preconditions.
NFV_PREFIX_SOURCE.json checks nine argument projections and nine matched
source mutations; this is an inventory, not a native proof.

Controlled request-encoder source cut: K058/K059 header, K070/K071 profile,
K072/K073 release, K074/K075 program, K076/K077 payment. Five arbitrary-index
positive windows PASS with five intended failing byte controls. K078 corrupts
a payment argument, K079 the error mapping, K080 the early guard; all FAIL at
intended assertions. Full typed payment Results, every error variant, guard
short circuits and child call counts are retained. The exact frozen encoder
body is checked after only the two local child-call substitutions and checked
constant-offset expansion. KMX exact configuration, deployed Pool features,
frozen offline graph and unchanged lock apply to every native run.

Model(y): NFV_Copy and NFV_ListFrames prove symbolic copy/frame operations;
NFV_Envelope.emitted returns the exact 320-byte five-window layout. Indexes
associate each native byte expression to that layout; RequestWindows covers
all bytes of the SAME returned array. RequestOracle.erase substitutes the
emitted payment models into the exact adopted caller. RequestGuards derives
U8 equality/zero-binding semantics by induction. All print standard axioms.
Native contract semantic transport is P6/D188 RECLASSIFICATION, not removal.
This cut supplies no production account-data or decoder-domain premise.

K067 with K068/K069 controls proves only restricted planner selected-program/
SAME request-allocation/byte forwarding. Empty account-data slices and typed
registry reply oracle are an explicit DOMAIN FINDING: they cannot instantiate
the production registry or account PacketDomains. No full prefix credit.

Still required: SAME production request decode/payment domains, admitted
master/checkpoint/lane state and borrow contexts, layout/payer/system checks,
marker/custody effects, and selected registry/program/account projections all
the way to invoke. No complete NFV_PoolReturnData.association or composed NDT
row is claimed. E001 small encoder extraction failed in Aeneas abstraction
merging after Charon success (exit2,66.683s,533408KiB,swap0); sole extraction
budget consumed, artifact archived, no rerun. Earlier process/HRTB failure
remains a tool boundary; the spine was not re-extracted.
""")
(E/'NFV_BRIDGES.md').write_text("""# Pool return-data bridge dispositions

Frozen source4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. New composed NDT rows0;
no headline closure and no NFV_PoolReturnData.association while B remains open.

| Member | Native / model evidence | Disposition |
|---|---|---|
| A account association |24 full index timeouts,8 stricter splits; NFV_AF_CERTIFICATE; Accounts.keys/flags/account_order | CLOSED-BY-RECLASSIFICATION(af3), retained std/allocator trust |
| B request encoder cut |5 positive windows,5 byte controls,3 argument/error/guard controls; emitted envelope/index/guard/oracle/window lemmas | Controlled source cut, outer SAME decoder/child domains OPEN |
| B planner |K067 with K068/K069 | Restricted EMPTY input-data metadata probe; no production prefix credit |
| B process/admission |9 source observations/mutations | OPEN native pre-state, effects and child PacketDomains |
| C SAME-object read/settlement |9 context-lifted observations+controls,2 context identity controls; retained K030/K034/K043; K051 excluded | Controlled post-admission cut; outer admitted context OPEN in B |
| C helper |K061 with4 byte/error/place/live-allocation controls; HelperModel.erase/same_emission | Controlled exact one-call cut under(y) |
| D composed association |NFD emit + A+B+C + NFR_ModelJoin | OPEN on B, no premise wrapper |

Every(y) use is native-contract semantic-transport P6/D188 RECLASSIFICATION,
never removal and no new trust row. The helper's two call substitutions are
reversible byte-for-byte; allocation executes real Box::new. The different-
allocation control keeps the first Box live. Seven nested format-error types
are covered. Same-emission derives encoder domain from the SAME original
valid statement. Nonempty RuntimeReturnData(792 here) remains the sole runtime
law in the existing model join. C's fixture input data is not promoted to
production admission. Full settlement writes/custody/marker effects are OPEN.
No field multiplication or SHA implementation runs in Kani; no new field stub.
Local full typed child oracles obey rule16. No Option<fn>-dependent credit,
writable static, quarantined receipt or renamed verdict repair is relied on.

K060 deliberately stopped after discovering the whole encoder frontier loop;
K066 own compile error; E001 Aeneas Unreachable. These earn no credit. Account
90s timeouts are not controls. The complete account copy bound337 accounts for
both allocations;205 is recorded incomplete. No caps or timeouts raised.

Audit:103 raw roots standard; same compiled driver8 matched fixtures pass.
All10 own proof modules zero unresolved; exactly650 inherited references in15
modules stay listed and not waived. Walker is byte-identical; driver diff is
module/root lists only. B043..050 receipts retain commands, source/import/tool
pins, exits, wall time, peak RSS, swap and printed axioms. No full release replay.
Own runner repairs are recorded in WORK_PLAN/transport receipts; infrastructure
was untouched. Cache exports/import hashes are retained; shipped sources and
three ELF hashes unchanged. Budget80K/50Lean/1extraction exhausted, no push.
""")
(E/'NFV_WORK_PLAN.md').write_text("""# Completed execution record

Authoritative attempt ledger:NFV_ATTEMPTS.jsonl, exactly80 Kani,50 Lean,1
extraction. Per-attempt immutable source/command/import/feature/graph/lock/cap/
exit/wall/RSS/swap/axiom receipts accompany it. No full unchanged regression
was repeated. Source changes explain focused proof retries and the final audit.

A completed prescribed per-index matrix, strict byte splits, complete337 copy
bound and adopted(af)(3) disposition. C completed20 context-lift receipts plus
helper source-cut controls and model association. B completed five native
request-byte windows and matched controls plus model envelope/frame/index/
guard/oracle interpretation, but the actual production prefix remains OPEN.
D therefore remains OPEN; no deceptive association premise/theorem or new NDT
closure. Final raw103-root audit/8 matched fixtures pass; own10 modules zero
unresolved,650 inherited references remain. Native/semantic transport remains
retained P6/D188 reclassification. All exact dispositions are in BRIDGES,
HANDOFF, REMAINING and CONE_DELTA.

Own-runner repairs: cargo metadata stderr separated and JSON parsed strictly;
B006 successful link recovered read-only after an absolute imported-C collector
path error, no compiler resubmission; K019 SSH255 recovered read-only after
submission, no Kani resubmission. Recovery retries fetch receipts only. Solver
temp cleanup tracks only paths opened by OWN native descendants. Timeout flags
are regenerated from immutable raw stdout. These repairs preserve or strengthen
validation and never edit launcher/reservation/shim/shared infrastructure.

The sole E001 extraction (small request helper, not HRTB spine) failed at Aeneas
abstraction merging after Charon; inputs/LLBC/pins archived once, no rerun and
no credit. All new pure/model top theorems print standard axioms. No independent
Lean-only prerequisite remains among these modules; remaining production
obligations need native caller/domain evidence and coupled model transport.

Own cache retained with hashed exports; imported read-only caches unchanged.
Only own build outputs/observed solver temps removed. All shipped repository
files unchanged; final three ELF hashes match, no rebuild claim. No file over
20MB, no __pycache__, no wallet/account key cleanup, no push.
""")
print('Four final handoff/audit files written from reviewed terminal evidence')
