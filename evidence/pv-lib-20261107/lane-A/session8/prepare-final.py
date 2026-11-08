"""Freeze new roots and qualified session metadata. Never reclassify slots."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path('evidence/pv-lib-20261107/lane-A/session8');A=E.parent;M=A.parent/'PLIB_MAP.json';base='1451aa2e0c9dfb974b4d846aed22c8407d5490ca'
sha=lambda b:hashlib.sha256(b).hexdigest()
support=[];roots=[];attempts=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());attempts.append({k:r[k] for k in ['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_sha256']})
 if not r['accepted'] or r['runtime_audit'] or 'RawAudit'in r['target']:continue
 raw=Path(r['source_path']).read_bytes();assert sha(raw)==r['source_sha256'],r['target']
 names=[re.match(r"'([^']+)'",v)[1]for v in r['axioms_summary_based']]
 assert names and all('sorryAx'not in v for v in r['axioms_summary_based'])
 support.append(dict(module=r['target'],source=r['source_path'],source_sha256=r['source_sha256'],attempt=r['attempt'],roots=names,qualification='Local symbolic/source-syntax support; not full source/OWNER adequacy or caller-history closure'))
 roots+=names
assert len(roots)==len(set(roots));modules=[r['module']for r in support]
(E/'SUPPORT.json').write_text(json.dumps(support,indent=2)+'\n');(E/'COMPILES.json').write_text(json.dumps(attempts,indent=2)+'\n')
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots),indent=2)+'\n')
s=Path('lean/PV_LIB_A_RawAudit7.lean').read_text();arrays='    (#[ '+', '.join('`'+m for m in modules)+'],\n     #[ '+', '.join('`'+r for r in roots)+'])'
s,n=re.subn(r'    \(#\[.*?\],\n     #\[.*?\]\)',lambda _:arrays,s,count=1,flags=re.S);assert n==1
Path('lean/PV_LIB_A_RawAudit8.lean').write_text(s)
old=json.loads(subprocess.check_output(['git','show',base+':'+str(M)]));current=json.loads(M.read_text());assert old['slots']==current['slots']and old['counts']==current['counts']
record=dict(base=base,legacy_definition='PV_LIB_StoreActionTable.v2',legacy_module='PV_LIB_A_StoreActionTable',legacy_v2_unchanged=True,
 definition='PV_LIB_StoreActionTable.v2TypedPrograms',step='PV_LIB_StoreActionTable.v2TypedStep',module='PV_LIB_A_StoreActionTable8',
 source_state='PV_LIB_StoreActionTable.SourceState',extends='PV_THR2_OwnInitInterpreterBridged.step via DeferredActions',
 typed248='PV_LIB_A_DropInPlace248',actual_destructor_methods='PV_LIB_A_ExactDestructMethods',
 cell_suffix='PV_LIB_A_CellDestruct504',cleanup_lowering='PV_LIB_A_UnwindMatchCorrectness.selection',all_reply_carrier_agreement='PV_LIB_A_UnwindReplies.full_reply',
 emitted_typed_bodies=[486,584,608,661,405,222],emitted_lowered_bodies=[644,454],
 complete_table=False,complete_D984_adequacy=False,caller_histories_completed=False,allocation_byte_images_defined=0,D991_applied=True,
 support='lane-A/session8/SUPPORT.json',findings='lane-A/session8/MODEL_FINDINGS.md',raw_audit='lane-A/session8/RAW_AUDIT.json',
 slot_status_changes=0,endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0,
 remaining=['opaque Option glue157','allocator erasure/type-to-glue reconstruction','arbitrary-T/dynamic callback native source effects','SOURCE/OWNER last-reference lifetime correspondence','collect4 and remaining opaque wrapper effects','Range93/f6/OwnInit corrected-machine caller histories'],
 qualification='PARTIAL. Typed dispatch/saved-old destruction and exact cleanup-preserving source bodies; no source adequacy, slot closure or caller-history promotion.')
current['lane_A_session8']=record;M.write_text(json.dumps(current,indent=2)+'\n');(E/'MAP_DELTA.json').write_text(json.dumps(dict(base=base,slots_changed=[],metadata=record,counts_unchanged=current['counts']),indent=2)+'\n')
oldtable=json.load(open(A/'session7/STORE_ACTIONS.json'))
(E/'STORE_ACTIONS.json').write_text(json.dumps(dict(legacy=oldtable,session8=record,all_inventory_entries_unchanged=True,inventory_accepted='D989'),indent=2)+'\n')
print(len(modules),'modules;',len(roots),'new roots; unchanged slots',current['counts'])
