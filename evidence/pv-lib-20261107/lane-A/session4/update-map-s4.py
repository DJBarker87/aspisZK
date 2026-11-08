"""Apply Lane B's pinned overlay and audited Lane A support; no row closure."""
import json,copy,hashlib,collections
from pathlib import Path
E=Path('evidence/pv-lib-20261107');A=E/'lane-A';S=A/'session4';p=E/'PLIB_MAP.json'
m=json.loads(p.read_text());before=copy.deepcopy(m)
base=json.loads((S/'BASELINE.json').read_text());bp=Path(base['lane_B_delta'])
assert hashlib.sha256(bp.read_bytes()).hexdigest()==base['lane_B_delta_sha256']
b=json.loads(bp.read_text());slots={s['slot']:s for s in m['slots']}
for incoming in b['slots']:
 if incoming.get('instance'):
  i=incoming['instance'];assert i['compiled'] and i['raw_audited']
  assert hashlib.sha256(Path('lean',i['module']+'.lean').read_bytes()).hexdigest()==i['source_sha256']
 slots[incoming['slot']].clear();slots[incoming['slot']].update(copy.deepcopy(incoming))
raw=json.loads((S/'RAW_AUDIT.json').read_text());assert raw['strict_raw'] and raw['unresolved']==0
roots={r['root'] for r in raw['roots']}
receipts=[json.loads(q.read_text()) for q in S.glob('receipt-*.json')]
def support(module,ns):
 r=next(r for r in receipts if r['target']==module and r['accepted'] and not r['runtime_audit'])
 assert hashlib.sha256(Path('lean',module+'.lean').read_bytes()).hexdigest()==r['source_sha256']
 names=[module+'.'+n for n in ns];assert set(names)<=roots
 return dict(module=module,roots=names,attempt=r['attempt'],source_sha256=r['source_sha256'],raw_audited=True,audit_attempt=raw['attempt'])
writer=support('PV_LIB_A_WriterSites',['source487','source930','source3447','source3519','source3641','source3756','source4327','source8248','selected','installed'])
owner=support('PV_LIB_A_OwnerStore',['agreement','installed','effects'])
transport=support('PV_LIB_A_OwnerStoreTransport',['advance_add','advance_agreement','segment','registry'])
actions=support('PV_LIB_A_OwnerStoreActions',['nonwaiting','completed'])
numbering=support('PV_LIB_A_WriterNumbering',['write_counter','local_store'])
range93=support('PV_LIB_A_RangeWriter',['range93'])
caller=support('PV_LIB_A_Caller124',['provider_pre','installed','counts'])
name=support('PV_LIB_A_NameValidity',['none_entry','some_entry'])
prefix=support('PV_LIB_A_PrefixTransport',['prefix_identity'])
ordinary=support('PV_LIB_A_WriterOrdinary',['noncatch','installed'])
registry=support('PV_LIB_A_WriterRegistry',['installed'])
for s in m['slots']:
 if s['parent'].startswith('thread') and s['child'] in ['thread:f9','thread:f10','thread:f93','thread:f167']:
  s['lane_A_session4_support']=dict(writer=writer,machine=owner,ordinary=ordinary,registry=registry,correction='D981: OWNER-aware OwnInitInterpreterBridged plus source-store meanings')
  s['reason']='Exact emitted token/operand inventory and issued-poll graph now bind W4 named meanings to the corrected OWNER-aware step. Continuous caller history, source reference provenance/age and native returned-value semantics remain missing; IntoIter/Vec runtime pointer/layout/reservation Values also remain unbound. No write-definedness premise or identity action is installed.'
  if s['child']=='thread:f93':
   s['lane_A_session4_support']['source_range']=range93
   s['reason']+=' Range93 now derives the local7 source Range write from its typed reference and constructor, without a Values or write-definedness premise; actual f15 cell history is still missing.'
facets={'thread:f361 :: atomicCounts':dict(caller124=caller),
 'thread:f361 :: nameValidity':dict(source_constructors=name),
 'thread:f6 :: machineTransport':dict(finite_prefix=prefix),
 'thread:OwnInit :: numbering':dict(local_source_writes=numbering),
 'thread:OwnInit :: resourceEnv':dict(same_resource_environment=actions),
 'thread:OwnInit :: registryFrame':dict(native_registry_frame=transport,writer_registry_frame=registry,retained_OWNER_actions=actions),
 'thread:f170 :: storeAction289':dict(corrected_machine=owner,inventory=writer),
 'thread:f15 :: storeAction93':dict(corrected_machine=owner,source_range=range93)}
for n,sup in facets.items():slots[n]['lane_A_session4_support']=sup
m['counts']=dict(collections.Counter(s['status'] for s in m['slots']))
m['lane_A_session4']=dict(base=base['base'],corrected_thread_step='PV_LIB_A_OwnerStore.step',extends='PV_THR2_OwnInitInterpreterBridged.step',meaning='PV_THR2_SourceStoreLibrary.interpret',away_agreement=owner,neutral_trace=transport,lane_B_delta_folded=base['lane_B_delta'],lane_B_delta_sha256=base['lane_B_delta_sha256'],qualification='Support and qualified deterministic graphs only. All actual-caller facets remain open. No endpoint/row closure, no implementation or trust change.',delta='lane-A/session4/MAP_DELTA.json')
before_slots={s['slot']:s for s in before['slots']}
changed=[dict(slot=s['slot'],before_status=before_slots[s['slot']]['status'],after_status=s['status'],after=s) for s in m['slots'] if s!=before_slots[s['slot']]]
(S/'MAP_DELTA.json').write_text(json.dumps(dict(base=base['base'],lane='A',lane_B_delta_folded=base['lane_B_delta'],changed_slots=changed,counts_before=before['counts'],counts_after=m['counts'],no_parent_or_endpoint_closure=True),indent=2)+'\n')
p.write_text(json.dumps(m,indent=2)+'\n');print(m['counts'])
