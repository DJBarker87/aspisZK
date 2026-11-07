"""Apply only audited Lane A changes; retain all other lane slots verbatim."""
from pathlib import Path
import json,hashlib,collections,copy
E=Path('evidence/pv-lib-20261107');A=E/'lane-A';p=E/'PLIB_MAP.json';m=json.load(open(p));before=copy.deepcopy(m)
assert json.load(open(A/'RAW_AUDIT.json'))['strict_raw']
receipts=[json.load(open(q)) for q in A.glob('receipt-*.json')]
def accepted(mod):
 r=[r for r in receipts if r['target']==mod and r['accepted'] and not r['runtime_audit']][-1]
 assert hashlib.sha256(Path('lean',mod+'.lean').read_bytes()).hexdigest()==r['source_sha256'];return r
def slot(name):return next(s for s in m['slots'] if s['slot']==name)
changed=[]
def install(s,mod,model,law,theorem,qualification,support):
 old=copy.deepcopy(s);r=accepted(mod)
 s['status']='INSTANTIATED';s['reason']=qualification
 s['instance']=dict(module=mod,model=model,law=law,theorem=theorem,root=s['root'],compiled=True,attempt=r['attempt'],source_sha256=r['source_sha256'],raw_audited=True,graph_of_function=True,qualification=qualification,audit_attempt=49482,supporting_roots=support)
 changed.append(dict(slot=s['slot'],before_status=old['status'],after_status=s['status'],instance=s['instance'],retained_reason=old['reason']))
for n in [277,278,279]:
 s=slot(f'thread:f170 -> thread:f{n}')
 qual=f'Exact CLOSED{n} graph at f170 native/source-operand boundaries. Existing named W4 memory/world/source-constructor facts are reused; source-store preservation is derived, all replies and malformed operands retained. New-interpreter poll transport is compiled. Full f170 source invariant, original-handler adequacy and continuous caller composition remain unproved; no parent row closure.'
 install(s,'PV_LIB_A_PurePoll',f'PV_LIB_A_NativeLeaves.model{n}',f'PV_LIB_A_NativeLeaves.law{n}',f'PV_LIB_A_PurePoll.installed{n}',qual,[f'PV_LIB_A_NativeLeaves.certified{n}',f'PV_LIB_A_PureCalls.certified{n}','PV_LIB_A_PureCalls.worlds', 'PV_LIB_A_PureCalls.asRef_source_local' if n==277 else f'PV_LIB_A_PureValues.source_local{n}'])
s=slot('thread:f170 -> thread:f280')
install(s,'PV_LIB_A_Residual280','PV_LIB_A_Residual280.model','PV_LIB_A_Residual280.law','PV_LIB_A_Residual280.certified','CLOSED280 deterministic native graph with W4 derived memory purity/new-interpreter poll transport, plus ONE new exact-function documented world/source-constructor fact. RESIDUAL280_SEMANTICS.json pins both Rust bodies and records the source-shaped counterexample to the generic CLOSED root. All answers and malformed operands retained. Original-handler adequacy, residual input provenance at the reached caller and full f170 composition remain unproved lower obligations, never new endpoint premises.',['PV_LIB_A_PurePoll.installed280','PV_LIB_A_PureCalls.certified280','PV_LIB_A_Residual280.source_local','PV_LIB_A_Residual280.old_contract_allows_ok','PV_LIB_A_Residual280.constructors_distinct'])
s=slot('thread:f537 -> thread:f612')
install(s,'PV_LIB_A_NativeLeaves','PV_LIB_A_NativeLeaves.model612','PV_LIB_A_NativeLeaves.law612','PV_LIB_A_NativeLeaves.certified612','CLOSED612 native-boundary graph plus exact emitted-token/returned-value/OWNER-lift binding to the existing Unique612 Fact. Every nonsuccess reply is retained; abort exposes its prefix only. Generic root source effects remain explicit; unsafe raw-pointer validity and enclosing537/458 caller/source composition are not discharged. No parent closure.',['PV_LIB_A_Unique612.installed','PV_LIB_A_UniqueBinding.callee','PV_LIB_A_UniqueBinding.installed'])
s=slot('slice:f7 :: typedDrop178')
drop=next(s for s in m['slots'] if s['parent']=='slice:f7' and 'Drop' in s['child'] and s['root'] is not None)
old=copy.deepcopy(s);s['root']=copy.deepcopy(drop['root'])
install(s,'PV_LIB_A_TypedDrop178','PV_LIB_A_TypedDrop178.model','PV_LIB_A_TypedDrop178.law','PV_LIB_A_TypedDrop178.installed','Typed Drop178 suffix graph at the actual f7 runtime carrier, from W2 RuntimeDrop.run/provider and f22 typed source projection, instantiating CLOSED W5 Drop. All reply arms retained, no chosen identity delta. Source call-entry cells/return descriptor and existing runtime DropSemantics are the literal provider conditions; f6 prefix and full f7 closure remain pending.',['PV_FN_SLICE_f7_RuntimeDrop.run','PV_FN_SLICE_f7_RuntimeDrop.provider'])
changed[-1]['before_root']=old['root']
s=slot('thread:f15 -> thread:f165')
install(s,'PV_LIB_A_Range165','PV_LIB_A_Range165.model','PV_LIB_A_Range165.law','PV_LIB_A_Range165.certified','Strengthened graph derived from CLOSED165 plus ONE new named documented-semantics fact for the exact IntoIterator identity function. Source/body pins and the typed Range counterexample to generic-root value binding are in lane-A/RANGE165_SEMANTICS.json. Every nonsuccess reply retained. Named source semantics/original-handler correspondence and continuous actual f15 binding remain lower obligations, never endpoint or desired-write premises.',['PV_LIB_A_Range165.reply_exact','PV_LIB_A_Range165.old_contract_allows_range','PV_LIB_A_Range165.sourceRange_distinct'])
for child in ['9','10','93','167']:
 for s in m['slots']:
  if s['status']=='MISSING-CHILD-LEMMA' and s['child']=='thread:f'+child:
   s['lane_A_support']=dict(native_graph='PV_LIB_A_WriterNative.certified'+child,source_graph='PV_LIB_A_SourceWriters.installed',meaning='PV_LIB_A_SourceWriters.meanings',status='SUPPORT ONLY: concrete Values/runtime reply semantics, reference-path/age and caller derivation remain missing',audit_attempt=49482)
   changed.append(dict(slot=s['slot'],before_status=s['status'],after_status=s['status'],support=s['lane_A_support']))
m['counts']=dict(collections.Counter(s['status'] for s in m['slots']))
assert sum(m['counts'].values())==170
m['lane_A_session3']=dict(base='5e397cb3878',qualification='Qualified graphs/support only; no ledger or parent closure, endpoint premises removed0/added0',delta='lane-A/MAP_DELTA.json',strict_audit=49482,other_lanes='Other lane deltas are not applied by this script.')
base_slots={s['slot']:s for s in before['slots']}
assessed=[]
for s in before['slots']:
 if (s['parent'].startswith('thread') and s['status']=='MISSING-CHILD-LEMMA') or s['slot']=='slice:f7 :: typedDrop178':
  now=slot(s['slot']);assessed.append(dict(slot=s['slot'],provider_status=s['provider_status'],before_status=s['status'],after_status=now['status'],qualification=now['reason']))
(A/'MAP_DELTA.json').write_text(json.dumps(dict(base='5e397cb3878',lane='A',changed_slots=changed,assigned_assessments=assessed,counts_before=before['counts'],counts_after=m['counts'],no_parent_or_endpoint_closure=True),indent=2)+'\n')
p.write_text(json.dumps(m,indent=2)+'\n')
print(m['counts'])
