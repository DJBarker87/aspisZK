from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14'
old=json.loads((D/'resume13/link-status.json').read_text());assert len(old)==36
updates={
'reconstruct_10':'New complete-Result shared-loan interpreter and continuation laws; exact six-step source map. Complete index/primitive/dependency association OPEN.',
'equality_value':'New complete-Result two-shared-loan interpreter, array-length and guard laws; exact six-step source map. Complete index/primitive/dependency association OPEN.',
'qm31_sum_products3_prepared':'New field-for-field private-payload adapter, two-sided roundtrip, complete array-index transport, and source-prepared Result transport. Actual source matrix/caller/std association OPEN.',
'selector_mask_sum_16':'Refuted total direct instance superseded by mask_on_domain + mask_call_domain. Source-shaped mask while/bit-clearing law, zero behavior, nonempty-domain witness and all frozen-trace index bounds compile; intrinsic/std source association remains OPEN.',
'at_point':'Refuted legacy-49 direct instance superseded by constructor_on_layout + constructor_call_layout + constructor_native. Exact local source-call resolution chooses 57; source expand/sum association OPEN.'}
lines=['# D493 V244 exact group/link status','',
'Runjoin op227 is **not discharged**. No endpoint premise was removed. V370 / pending owner D381,D386 retained; no new T item.','',
'`selected_callback14` and the typed `selected_all_groups14` schema compile, with joint explicit model witnesses and byte-identical bridge conclusions. The complete deployed std/dependency signature catalogue is not instantiated. Accordingly, the requested concrete all-group source decomposition is **not complete**; the generic schema is not credited as deployed closure.','',
'| Missing body | Status |','|---|---|',
'| private_public | Reused b3p6-1 exact-span binding from resume13. |',
'| withdrawal_public | Reused b3p6-1 exact-span binding from resume13. |',
'| semantic | Reused exact emitted match and carrier binding from resume13. |',
'| frontier | Exact declaration-body lift, pinned extraction with fields opaque, body-identical callee-parameter port, twenty named continuation factorizations and their composition compile. Local b3p6-1 credit; fields/Vec caller closure OPEN. |',
'| transition | Exact two-arm deployed source checked; shared loan identity and any caller continuation preserved; value erasure reaches prior transition model. No callees, stores or destructors. Local own-1 binding; compiler boundary retained. |',
'| fields | Extractor refuses escaping iterator references. New forward cursor/source loop and complete partial-output/error/fail/div model law compile. Vec append/native allocation association OPEN; no b3p6-1 extraction credit. |',
'| terminal_qm31 | Free root reaches exact owned method; pinned extractor internal error, including changed semantic-callee boundary. Source wrapper equation remains a native Link. No body credit. |','',
'| Changed function | Model/context instance | Native association |','|---|---|---|']
for r in old:
 name=r['function'];status=updates.get(name,'OPEN: no complete source/dependency association credited.')
 r['resume14_native_status']=status;r['new_fully_composed_own1_bound']=False
 lines.append('| '+name+' | `'+r.get('model_theorem','OPEN')+'` | '+status+' |')
lines+=['',
'18/36 prior model/context instances are retained. **0/36 complete changed-function native/dependency associations** are newly closed. The new local immutable helper dossiers and prepared adapter are not counted as full native closure.','',
'| Other link/group | Status |','|---|---|',
'| Added mask caller domain | Frozen-table model witness and caller transport compile. Complete native active caller association remains explicit. |',
'| Added constructor layout | Constant-57 model law and exact local source resolution checked; no restriction on input points and no reachability pruning. Native constructor/expand/sum obligation retained. |',
'| D188 | Generic complete-Result borrow/store refinement and readback law compile. Earlier 16 finite native helper comparisons/negative control reused unchanged. Complete per-helper/caller restoration association OPEN. |',
'| Matrix | Generic nested mutable-borrow refinement, typed row handling, readback and all bounded-write prefix trace equality compile. New prepared payload/array adapter transports Results. Earlier 270 snapshots/2430 entries and ten terminal results reused as finite validation. Actual deployed matrix observation/source association OPEN. |',
'| Slice | New immutable forward-cursor creation/end/advance/backing preservation and fields caller transport compile; reverse Range bounds/step laws compile. Earlier four-slot mutable caller model retained. Complete native pointer/borrow constructors, drop and pre-inline source coverage OPEN. |',
'| Std/dependency closure | Typed family predicate and its model witness compile, but no exhaustive pinned concrete source-cone signature table is supplied. Full closure OPEN. Compiler-generated glue/intrinsic semantics remain named at V370/D381,D386, never T. |','']
(O/'link-status.json').write_text(json.dumps(old,indent=2)+'\n');(O/'GROUP-STATUS.md').write_text('\n'.join(lines))
