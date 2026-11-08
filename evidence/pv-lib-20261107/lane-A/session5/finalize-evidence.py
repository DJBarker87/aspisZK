"""Evidence assembly only. Does not launch or repeat a proof/audit."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,collections
E=Path(__file__).parent;A=E.parent;R=A.parent
records=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());records.append(r)
 if not r['accepted']:
  raw=subprocess.check_output(['git','cat-file','blob',r['source_index_blob']])
  assert hashlib.sha256(raw).hexdigest()==r['source_sha256']
  (E/f"failed-{r['attempt']}.lean.xz").write_bytes(lzma.compress(raw))
accepted={r['target']:r for r in records if r['accepted'] and not r['runtime_audit']}
def support(m):
 r=accepted[m];p=Path('lean',m+'.lean');raw=p.read_text();assert hashlib.sha256(raw.encode()).hexdigest()==r['source_sha256']
 return dict(raw_audited=(E/'RAW_AUDIT.json').exists(),audit_attempt=47490 if (E/'RAW_AUDIT.json').exists() else None,module=m,source=str(p),source_sha256=r['source_sha256'],attempt=r['attempt'],roots=[m+'.'+n for n in re.findall(r'^#print axioms (\S+)',raw,re.M)],qualification='SUPPORT ONLY; no row/endpoint closure')
supports={m:support(m) for m in json.loads((E/'AUDIT_ROOTS.json').read_text())['modules']}
table=json.loads((E/'STORE_ACTIONS.json').read_text());table['candidate']='PV_LIB_A_DropDispatchV2.step';table['base']='PV_THR2_OwnInitInterpreterBridged.step'
for e in table['new_entries']:
 if e['function'] in {'thread:f504','thread:f641'}:
  n='CellBoolSet504' if e['function']=='thread:f504' else 'CellTake641';m='PV_LIB_A_CellSourceV2'
  e.update(meaning=m+'.PV_THR2_LibrarySemantics_'+n,source=supports[m]['source'],source_sha256=supports[m]['source_sha256'],attempt=supports[m]['attempt'],coverage=('BOOL ONLY; arbitrary-T old-value destructor unsupported' if n=='CellBoolSet504' else 'TRANSPARENT SpawnHooks specialization; native old-value return/backing fact still unbound'))
for i,n,coverage in [(486,'ArcDropNonlast486','NONLAST source count >1 ONLY; last payload destructor not modeled'),(683,'WeakDropNonlast683','NONLAST allocated Weak count >1 ONLY; dangling/last/deallocation not modeled'),(369,'OptionTake369','Source None write; actual native old-value return/backing fact still unbound')]:
 m='PV_LIB_A_DropStoreV2';table['new_entries'].append(dict(function='thread:f'+str(i),meaning=m+'.PV_THR2_LibrarySemantics_'+n,source=supports[m]['source'],source_sha256=supports[m]['source_sha256'],attempt=supports[m]['attempt'],coverage=coverage))
table['new_entries']=list({e['function']:e for e in table['new_entries']}.values())
table['not_installed_full_destructors']=['Arc486 last-strong payload Drop and implicit Weak guard','Weak683 dangling/last branch and deallocation','Arc584 drop_slow with unwind','typed builtin Drop exact-type composition','Cell504 arbitrary-T old-value Drop','native wrappers and callback source effects']
table['superseded_incorrect_drafts']=[table.pop('superseded_incorrect_draft', 'PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicBoolStore646'),'PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CellSet504','PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641']
table['complete_D984_adequacy']=False
table['agreement']=supports['PV_LIB_A_DropDispatchV2'];table['Cell_correction_agreement']=supports['PV_LIB_A_OwnerStoreV3']
table['read_value_facts']=supports['PV_LIB_A_AtomicReadsV2'];table['new_lower_value_facts']=[supports['PV_LIB_A_AtomicBoolNewV2'],supports['PV_LIB_A_CellSourceV2']]
inv=json.loads((A/'store-write-leaves-v2.json').read_text());installed={e['function']:e for e in table['new_entries']}
table['all_inventory_entries']=[dict(function=e['id'],emission=e['emission'],sites=e['sites'],affected_rows=e['affected_rows'],meaning=installed.get(e['id'],{}).get('meaning',e.get('named_meaning') if e['id'] in {'thread:f9','thread:f10','thread:f93','thread:f167','thread:f289'} else None),coverage=installed.get(e['id'],{}).get('coverage','RETAINED V1; caller/value bindings open' if e['id'] in {'thread:f9','thread:f10','thread:f93','thread:f167','thread:f289'} else 'OPEN: no full named semantics or installed action; do not credit as corrected')) for e in inv['source_writers']]
(E/'STORE_ACTIONS.json').write_text(json.dumps(table,indent=2)+'\n')
(E/'SUPPORT.json').write_text(json.dumps(supports,indent=2)+'\n')
compiles=[{k:r.get(k) for k in ['attempt','target','runtime_audit','exit','accepted','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256','axioms_summary_based']} for r in records]
(E/'COMPILES.json').write_text(json.dumps(compiles,indent=2)+'\n')
# Only append evidence; statuses and the complete Lane B folding are retained.
p=R/'PLIB_MAP.json';x=json.loads(p.read_text());before={s['slot']:s['status'] for s in x['slots']};delta=[]
for s in x['slots']:
 names=[];note=''
 if s['child'] in {'thread:f9','thread:f10','thread:f93','thread:f167'}:names+=['PV_LIB_A_DropDispatchV2'];note='D984 native/wrapper backing and complete caller history remain open.'
 if s['child']=='thread:f360':names+=['PV_LIB_A_ArcPollV3','PV_LIB_A_ArcMemoryV2'];note='Local corrected12950 poll/count action only. Historical graph does not establish complete D984 source adequacy; Builder270 site10098 still lacks its own history.'
 if s['child']=='thread:f165' or s['slot']=='thread:f15 :: storeAction93':names+=['PV_LIB_A_RangeHistoryV2','PV_LIB_A_RangeTraceV2'];note='FIRST local7 history and first93 action only; continuous prefix currently ORIGINAL interpreter, corrected-owner and later-loop invariant open.'
 facets={'thread:f6 :: machineTransport':['PV_LIB_A_F6DeliveryTransportV2'],'thread:f361 :: arcCloneValueFrame':['PV_LIB_A_CloneValidityV2','PV_LIB_A_CloneIssuedV2','PV_LIB_A_ClonePrologueV2','PV_LIB_A_CloneCountV2'],'thread:f361 :: atomicCounts':['PV_LIB_A_AtomicReadsV2','PV_LIB_A_AtomicBoolNewV2','PV_LIB_A_CloneCountV2'],'thread:OwnInit :: numbering':['PV_LIB_A_StoreCounterV2'],'thread:OwnInit :: registryFrame':['PV_LIB_A_WriterRegistryV2'],'thread:OwnInit :: resourceEnv':['PV_LIB_A_DropDispatchV2']}
 if s['slot'] in facets:names+=facets[s['slot']];note='Local support only. Actual original-entry/handler/complete source history and resource-environment bindings remain open.'
 if names:
  s['lane_A_session5_support']=dict(support=[supports[m] for m in dict.fromkeys(names)],qualification=note,audit='lane-A/session5/RAW_AUDIT.json')
  delta.append(dict(slot=s['slot'],status_before=s['status'],status_after=s['status'],support=s['lane_A_session5_support']))
assert before=={s['slot']:s['status'] for s in x['slots']}
x['lane_A_session4']['superseded_machine_qualification']='D981 old-five step misses D984 Arc/source writes. Historical graphs are not full D984 adequacy.'
x['lane_A_session5']=dict(base='bbb785242b876aa943e9627aa46a7ffa350a860a',ruling='D984 thread-26 double-prime',candidate_thread_step=table['candidate'],extends=table['base'],complete_D984_adequacy=False,inventory='lane-A/store-write-leaves-v2.json',table='lane-A/session5/STORE_ACTIONS.json',support='lane-A/session5/SUPPORT.json',raw_audit='lane-A/session5/RAW_AUDIT.json',qualification='PARTIAL, not a fully corrected source machine. Last/type-dependent Drop, arbitrary-T Cell set and opaque wrappers remain unbound. No row consumer/ledger/endpoint/T changes.',endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0,f6_cache='68 pinned dependency replays46320-46387; all74 f6 modules now available; cache preparation only',delta='lane-A/session5/MAP_DELTA.json')
p.write_text(json.dumps(x,indent=2)+'\n');(E/'MAP_DELTA.json').write_text(json.dumps(dict(base='bbb785242b8',changes=delta,status_changes=0,counts=x['counts']),indent=2)+'\n')
print(len(records),'receipts;',len(supports),'new modules;',len(delta),'support updates; statuses unchanged')
