from pathlib import Path
import json
E=Path(__file__).parent;root=E.parent.parent
support={
 'thread:f15 :: storeAction93':('PV_LIB_A_RangeIteration13.history','Any live iterator induction facet executes preparation/full93/Some-or-None/captures/166-to270 prefix. NextIteration13 joins post3519 source storage/backedge to that prefix. Administrative call-entry/return frames checked; prior-callee internal frame and whole-loop induction remain open.'),
 'thread:f6 :: machineTransport':('PV_LIB_A_F6IssuedHistory13.history','Continuous corrected f6 BODY-entry through FULL121/122/123/124, source captures, actual125/219, FULL134 and issued9196. Native value/physical/frame bindings, original-entry-to-f6, callback linkage/220/208-to3400, full f6 Post and14756 remain open.'),
 'thread:f6 -> thread:f125':('PV_LIB_A_F6IssuedHistory13.history','Actual1989 structured125 is EXECUTED in the continuous BODY-entry source prefix, including generated source capture construction. No successful native representation instance or whole f125/f6 Post claimed.'),
 'thread:f125 -> thread:f219':('PV_LIB_A_F125Enter21913.run','Actual5017 source operands and structured219 entry; failed operands remain gaps. Included in the continuous f6 history; no native assumption or whole219 Post.'),
 'thread:f219 -> thread:f134':('PV_LIB_A_F219Full13413.run','Actual9182 issue/full native reply retained in continuous f6 prefix. Does not instantiate native ManuallyDrop value/physical law.'),
 'thread:f219 -> thread:f318':('PV_LIB_A_F219Issue31813.run','Actual9196 issuance after source Data/callback construction; continuous f6 history ends at that request. Source selector linkage to actual316 entry remains open.'),
 'thread:f318 -> thread:f316':('PV_LIB_A_IntrinsicInvoke13.actual','Local exact9196 selected request invokes316 with actual source address and SAME full suspended parent. Not yet linked to the continuous f6 result; no native/source/binary adequacy claimed.'),
 'thread:f316 -> thread:f410':('PV_LIB_A_F316Full41013.run','Actual callback11176 issue and FULL410 reply on corrected phase machine; all source failures retained. Native take value/FnOnce shape law remains separate.'),
 'thread:f316 -> thread:f220':('PV_LIB_A_F316History13.run','Separate continuous316 BODY-entry through FULL410/preparation and source metadata-selected11187 entry220, or first stop. Original f6-to316 linkage and220/208/15 continuation remain open.')}
meta=dict(base='6dbfb38c6d1102dd828a716e9412043febf6c0da',target='D999 OwnInit prefix through14756; source7 closure',
 rule='D999/thread-5; no deferred callee/destructor replay; local requested backedge storage only',
 prefix_support={k:dict(theorem=v[0],module=v[0].rsplit('.',1)[0],qualification=v[1]) for k,v in support.items()},
 table_surface='PV_LIB_A_StoreActionTable13; SAME partial phase-bearing machine; legacy v2 unchanged',
 row_closures=0,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,byte_images_defined=0,
 completion='PARTIAL: requested completion NOT achieved; no new361-through14756 or joint witness')
p=root/'PLIB_MAP.json';m=json.loads(p.read_text());m['lane_A_session13']=meta
for slot in m['slots']:
 if slot['slot'] in meta['prefix_support']:slot['session13_prefix_support']=meta['prefix_support'][slot['slot']]
p.write_text(json.dumps(m,indent=2)+'\n')
(E/'MAP_DELTA.json').write_text(json.dumps(dict(scope=meta,slot_support=meta['prefix_support'],status_changes=0),indent=2)+'\n')
