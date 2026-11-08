"""Assemble exact new proof roots and qualified metadata; no slot reclassification."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path('evidence/pv-lib-20261107/lane-A/session7');A=E.parent;M=Path('evidence/pv-lib-20261107/PLIB_MAP.json');base='03c3c72b1436a3cd5677265b0682a9490a4f4878'
sha=lambda b:hashlib.sha256(b).hexdigest()
support=[];roots=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text())
 if not r['accepted']or r['runtime_audit']or'RawAudit'in r['target']:continue
 raw=Path(r['source_path']).read_bytes();assert sha(raw)==r['source_sha256']
 names=[re.match(r"'([^']+)'",v)[1]for v in r['axioms_summary_based']]
 assert names and all('sorryAx'not in v for v in r['axioms_summary_based'])
 support.append(dict(module=r['target'],source=r['source_path'],source_sha256=r['source_sha256'],attempt=r['attempt'],roots=names,qualification='Local mathematical/source-syntax support only; no slot or source-adequacy closure'))
 roots+=names
assert len(roots)==len(set(roots))
(E/'SUPPORT.json').write_text(json.dumps(support,indent=2)+'\n');modules=[r['module']for r in support]
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots),indent=2)+'\n')
s=Path('lean/PV_LIB_A_RawAudit6.lean').read_text();arrays='    (#[ '+', '.join('`'+m for m in modules)+'],\n     #[ '+', '.join('`'+r for r in roots)+'])'
s,n=re.subn(r'    \(#\[.*?\],\n     #\[.*?\]\)',lambda _:arrays,s,count=1,flags=re.S);assert n==1
Path('lean/PV_LIB_A_RawAudit7.lean').write_text(s)
old=json.loads((A/'session6/STORE_ACTIONS.json').read_text());current=[]
updates={
 'thread:f504':('PV_LIB_A_CellSetThreadId.PV_THR2_LibrarySemantics_CellSetCopy504','Exact copy specializations417/437/477/629 only; arbitrary-T and nonempty SpawnHooks still unsupplied'),
 'thread:f683':('PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683; PV_LIB_A_WeakDropSource.finish','Source-backed decrement/dangling/deallocation completion only; OWNER allocator/registry/backing adequacy unbound'),
 'thread:f214':('PV_LIB_A_ThreadCloneStore.PV_THR2_LibrarySemantics_ThreadCloneSource214','Source-backed Thread->Pin->Arc count only; OWNER-only backing and native value/world binding unbound')}
for r in old['all_inventory_entries']:
 r=dict(r);r['current_meaning']=r['meaning'];r['current_coverage']=r['coverage'];r['included_in_v2Source']=r['included_in_partial_v2']
 if r['function']in updates:r['current_meaning'],r['current_coverage']=updates[r['function']];r['included_in_v2Source']=True
 current.append(r)
table=dict(base=base,inventory_accepted='D989; retained unchanged',legacy_definition='PV_LIB_StoreActionTable.v2',legacy_module='PV_LIB_A_StoreActionTable',definition='PV_LIB_StoreActionTable.v2Source',module='PV_LIB_A_StoreActionTable7',native_step='PV_LIB_A_DeferredActions.step',sized608_step='PV_LIB_A_TypedDropSource.step',sized608_resolver='PV_LIB_A_EmittedDropBinding.programs',complete_table=False,complete_D984_adequacy=False,arbitrary_T_cell504=False,last_reference_destructors=False,opaque_wrapper_effects=False,supplied_projection_count=sum(r['included_in_v2Source']for r in current),missing_candidate_meanings=sum(r['current_meaning']is None for r in current),all_inventory_entries=current,qualification='PARTIAL source support only. Intermediate ActionPolling/Table7 retry graphs are superseded for the four deferred actions; no caller-history promotion.')
(E/'STORE_ACTIONS.json').write_text(json.dumps(table,indent=2)+'\n')
m=json.loads(M.read_text());previous=json.loads(subprocess.check_output(['git','show',base+':'+str(M)]));assert m['slots']==previous['slots']and m['counts']==previous['counts']
record=dict(base=base,table_definition=table['definition'],legacy_v2_retained=True,table_module=table['module'],candidate_native_step=table['native_step'],candidate_sized608_step=table['sized608_step'],sized608_resolver=table['sized608_resolver'],extends='PV_THR2_OwnInitInterpreterBridged.step',complete_table=False,complete_D984_adequacy=False,caller_histories_completed=False,inventory_unchanged=True,table='lane-A/session7/STORE_ACTIONS.json',support='lane-A/session7/SUPPORT.json',checked_gaps='lane-A/session7/MODEL_FINDINGS.md',raw_audit='lane-A/session7/RAW_AUDIT.json',qualified_projection_count=table['supplied_projection_count'],missing_candidate_meanings=table['missing_candidate_meanings'],slot_status_changes=0,endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0,qualification='PARTIAL. Four exact copy504 specializations, staged SOURCE Weak completion, source-backed214, and exact sized608 dispatch. Arbitrary-T/nonempty hooks/last-strong/native wrappers and caller histories remain open; no closure credit.')
m['lane_A_session7']=record;M.write_text(json.dumps(m,indent=2)+'\n')
(E/'MAP_DELTA.json').write_text(json.dumps(dict(base=base,slots_changed=[],metadata=record,counts_unchanged=m['counts']),indent=2)+'\n')
print(len(modules),'modules;',len(roots),'new roots;',table['supplied_projection_count'],'qualified projections;',table['missing_candidate_meanings'],'missing meanings')
