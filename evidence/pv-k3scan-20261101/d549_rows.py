from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
c=json.loads(lzma.decompress((E/'CREDITS.json.xz').read_bytes()));by={x['credit_id']:x for x in c};touched=sorted({r for x in c for r in x['ledger_rows']},key=lambda x:(int(x[1:].split('-')[0]),x));assert len(touched)==34
scope={
'V163':('Conditional whole-data/model/caller statement laws; actual deployed data equation remains OPEN.','No suspended observation supplies the missing native/data equation.'),
'V164':('PV_Op223_V164.refinement: all raw inputs, ordered complete Result, explicit primitives.','Recount-8 structural K-1 substitute; the bounded arity-zero diagnostic is independent.'),
'V165':('Native representation remains OPEN; retained typed/model transports are conditional.','Historical source-root examples do not discharge the actual native carrier.'),
'V167':('Native effects/world/physical observation remain OPEN.','Retained model/source-helper laws do not consume suspended native-root examples.'),
'V169':('Four concrete Default dictionaries, owned take/frame, explicit fixed types.','Extraction plus deployed structural transport; arbitrary Default/Drop is unclaimed.'),
'V177':('Selected bounded PathBuf deref P6 gate plus op25_source law.','C044 has the controlled PathBuf pair; deployed std transfer remains withheld.'),
'V178':('OPEN diagnostic/path/IO scope; retained conditional source helpers.','Old bounded join observations supply no current native/deployed closure.'),
'V179':('Complete-body structural String-to-Path binding and existing valid String carrier.','K-1 substitute; historical copied native gates remain independently suspended.'),
'V180':('Selected bounded PathBuf as_ref P6 gate plus op29_source law.','Shares C044; lifetime/representation and std/compiler boundaries remain.'),
'V181':('OPEN allocation/diagnostic scope.','The old capacity diagnostic does not close allocation/public-failure behaviour.'),
'V182':('op31_source: representable append buffer/tail, first error, snapshot copy, post-header/world.','Current structural append packet is independent of historical ASCII/copy gates.'),
'V183':('INSTALLED op32 allocator family: ReserveSelected.complete / AllocatorWorld63.','World-indexed complete Result, metadata/error encoding and post-world; historical C018/C019/C029 are not premises.'),
'V184':('MoveClosure.complete: non-Copy/ZST move, ownership/frame and allocation unchanged.','Current structural packet preserves the old copying-reference counterexample; old Kani is independent.'),
'V185':('Original bounded Word/Error is_empty P6 gate and op34_source law.','C042 fresh pair clears K-3 only; C051 native Drop log does not support this current gate; std transfer is withheld.'),
'V186':('Generic Vec::new/default constructor source law; ZST capacity retained.','Structural constructor packet; no dependence on the older Word default test.'),
'V187':('Generic owned Vec-to-array Result, mismatch retains input, explicit finalization effects.','Current structural source packet does not consume C051 native Token::drop logging.'),
'V195':('INSTALLED op51 value selection with qualified arbitrary-limb serializer source packet.','Structural complete copy/frame and checked ManuallyDrop restoration; old byte-copy Kani is independent.'),
'V219':('INSTALLED op120 boundary value selection and all-raw28 complete ordered source packet.','Structural/extraction source qualification; no historical arithmetic diagnostic is a premise.'),
'V232':('OPEN SHA update-block/source callback boundary; retained bounded load/store helper checks.','C176/C178 are UNAFFECTED; no suspended observation supplies the missing backend law.'),
'V233':('Structural layout/size/geometry facts; typed GenericArray64/consumed bridge remains SUSPENDED.','rdcd4 explicitly withholds native typed association. C002 no-stub support stays suspended; fresh C088/C089 preserve their separate original stubbed scopes.'),
'V234':('DigestFinal.selected_native: complete Result/carrier with finalizer/compression parameters.','Current dlib2 structural wrapper; C052 padding checks do not supply a SHA/native backend law.'),
'V235':('FixedFinal.selected_native: complete Result/carrier with finalizer/compression parameters.','Same parameterized structural boundary; SHA-NI and native backend remain open.'),
'V237':('Latest rdcd4 generic Core Result plus fixed64 default singleton source packet.','Latest restoration uses zero Kani; old C050/C053 observations do not support it.'),
'V240':('Complete all-raw/slice compression source law and deployed index-loop caller.','Qualified structural/extraction route, exact five operations; old recurrence/iterator Kani is independent.'),
'V244':('OPEN op227; current 36/36 local-body associations include two Kani bodies.','Current Kani support is C155 reconstruct_10 and C157 validate_transition. Direct/structural mask/sum routes do not consume old memo credits C156/C163/C164.'),
'V256':('Original gamma iterator/current-array/FnMut/carry and continuation source packet.','Qualified original extraction/structural binding, including indexed writes; old gamma Kani is independent.'),
'V260':('Original253/selected251 APIs, all weights/kinds/indices and complete errors/divergence.','Qualified source range/fold/index bindings and original resource world; old word/carry Kani is independent.'),
'V264':('All-slots selected structural source, arbitrary masks/rows/raw limbs and complete errors.','No dependence on historical pole diagnostics for the current source packet.'),
'V352':('OPEN L2; canonical/decoded guard, event and trace helper laws.','D371 retains whole-native execution and native parser associations as P; old C101-C109/C243 are not used to prove them.'),
'V354':('OPEN L2; source/model sampler/control/decoded guard laws.','Same D371 structural/owned boundary; no new whole-native observer law is credited.'),
'V357':('OPEN L2; conditional helper/materialization/guard and trace laws.','Whole native helper/inverse/caller transport remains named P; old parser observations do not discharge it.'),
'V360':('OPEN L2; decoded honest sumcheck/control and trace laws.','Native oracle/interpolation/running-claim transport remains P; suspended examples provide no closure.'),
'V380-inversion':('Conditional same-coin pole/guard containment, slot/order/mask algebra; full native slots OPEN.','Current Lean/source laws do not consume suspended C056 copying support; original coupling and zero-boundary remain.'),
'V389':('REDUCED conditional P6/native-association rule at exact recorded scopes.','Suspended applications are excluded. The retained external law is a named hypothesis, never a new T field.')}
assert set(scope)==set(touched)
current={'V232':['C176','C178'],'V177':['C044'],'V180':['C044'],'V185':['C042'],'V244':['C155','C157']}
rows=[]
for rid in touched:
 deps=current.get(rid,[]);bad=[cid for cid in deps if by[cid]['final_status']=='SUSPENDED'];historical=[x['credit_id']for x in c if rid in x['ledger_rows'] and x['final_status']=='SUSPENDED']
 rows.append({'ledger_row':rid,'current_credited_scope':scope[rid][0],'current_kani_support':deps,'depends_on_still_suspended_credit':bool(bad),'suspended_current_support':bad,'historical_suspended_observations':historical,'basis':scope[rid][1]})
s=json.loads((E/'D549-RESULTS.json').read_text());raw=(json.dumps({'scope_pins':'CURRENT-SCOPE-PINS.json + CURRENT-SCOPE-ADDENDUM.json + CURRENT-SCOPE-REFRESH-D549.json; RDCD4 report at 505f8745ee0a99d3c0ae16cb5f8217ec35dfcc77','campaign_in_progress':s['campaign_in_progress'],'rows':rows},indent=2)+'\n').encode();(E/'K3-ROWS.json').write_bytes(raw)
intro='''# D549 current-scope rollup: all 34 touched ledger rows\n\nThis answers whether the CURRENT credited scope requires a credit whose final status is still SUSPENDED. It preserves the actual structural, extraction, model and bounded P6 qualifications. It does not assert whole-row closure, native world composition, deployed std parity or the privacy target. The ledger is unchanged.\n\nCurrent source pins and copied statements are in CURRENT-SCOPE-PINS.json, CURRENT-SCOPE-ADDENDUM.json + CURRENT-SCOPE-REFRESH-D549.json and current-scope/. Per-credit suspensions and exact fresh pairs are in K3-CREDITS.md / CREDITS.json.xz. K3-ROWS.json lists every historical suspended observation separately, so a NO below never erases it.\n\nThe current bounded P6 dependencies that require a controlled K-3 check are C044 (V177/V180), C042 (V185), and C155/C157 (V244's two currently consumed Kani local bodies). V232 also retains the unchanged UNAFFECTED C176/C178 load/store helper checks. All other retained scopes below have an independent source/model route, or explicitly retain the native association as unproved. V233's copied old no-stub P6 description is not clearance of C002 or of the unproved typed-carrier bridge.\n\n'''
intro+=('Campaign complete: sixty charged invocations.\n\n'if not s['campaign_in_progress']else'CHECKPOINT: rerun campaign remains in progress.\n\n')
intro+='| Row | Current credited scope | Depends on a still-SUSPENDED credit? | Reason / retained boundary |\n|---|---|---|---|\n'
for r in rows:intro+='| '+r['ledger_row']+' | '+r['current_credited_scope']+' | **'+('YES: '+', '.join(r['suspended_current_support'])if r['depends_on_still_suspended_credit']else'NO')+'** | '+r['basis']+' |\n'
intro+='\nNative-step static credits C051 (Token::drop/DROPS) and C053 (Core::default/DEFAULT_STATE), and old shared-memo credits C156/C163/C164, remain SUSPENDED. No local mock replaces those native/stub steps. Current wrapper/move/default/local-body scopes above do not consume them.\n\nAll original E1/E2, actual native RunJoin/carrier/world/allocator adequacy, compiler V370/D381/D386, proof-account client and L1/L2/L3 boundaries remain. Endpoint premises removed/added/weakened by this audit: 0/0/0.\n'
(E/'K3-ROWS.md').write_text(intro);print(len(rows),'rows;',sum(r['depends_on_still_suspended_credit']for r in rows),'current scopes depend on suspended credits')
