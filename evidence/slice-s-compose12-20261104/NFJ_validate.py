"""Add-only scanner certificate; all NFH/NFD/NDT gates remain unchanged."""
from pathlib import Path
import sys,json,copy,hashlib,re
from functools import lru_cache
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-s-compose11-20261104'))
import NFH_validate as inherited
from NFJ_source_checks import F,REV,all_native,review
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
FLAGS=['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']
TRUST=dict(id='RuntimeMemcmp',medium='ADDED runtime trust; pending owner confirmation',ruling='ac',scope='RuntimeMemcmp688Zero: SAME valid readable 688-byte ranges; normal return to supplied i32 slot; zero iff byte-equal; no other observable effect; no ordering, sign or timing',evidence=['docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md','evidence/slice-s-compose11-20261104/NFH_COMPARISON_FINDING.md'])
NAMES=['NFJ_Comparison.'+n for n in ['header_length','same_buffer_lengths','nativeEqualityBridge','slot_zero_iff','completion']]+['NFJ_Scanner.'+n for n in ['result_state_effects','encode_domain','decode_domain','tag_domain']]
HYPOTHESES=[F+'.PacketDomain',F+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA','RuntimeMemcmp (ac), ADDED trust']
PRIMITIVES={
 'external:TX2:226:3':'ok_or: same InvalidAccountData on checked-add None; NFD_K134/135',
 'external:TX2:226:4':'checked_add: 688+57607=58295, no overflow; NFD_K134/135',
 'external:TX2:226:5':'len: exact borrowed length gate; NFD_K134/135',
 'external:TX2:226:6':'Err: exact InvalidAccountData on wrong length; NFD_K134/135',
 'external:TX2:226:7':'Box::new: same decoded value/allocation and exact cleanup under (aa)/Allocator; NFD_K138..145',
 'external:TX2:226:8':'decode map_err: every child error mapped to InvalidAccountData, no success fabrication; NFD_K138..145',
 'external:TX2:226:9':'as_ref: SAME successful [u8;688] encoded allocation, SAME header, slot-zero test; NFJ_K003..014 and RuntimeMemcmp(ac)',
 'external:TX2:226:10':'encode map_err: every child error mapped to InvalidAccountData, comparison not reached; NFD_K146/147',
 'external:TX2:226:11':'Err: unchanged unequal/tag branch continuation; NFD_K146/147, NFJ_K003/008/009',
 'external:TX2:226:12':'Ok: same candidate Box and proof_length57607, no later comparison observer; NFD_K146/147, NFJ_K003/008/009'}
CLASSIFICATIONS={
 'crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag':'S2 exact typed variant; all-variant CLOSED child; byte696 tested only after equality',
 'crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1':'SAME immutable header bytes[0..688]; all raw688-byte decoder domain; exact Result/error and owned Box carrier',
 'crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1':'SAME decoded Box value; all-raw typed candidate domain including validation errors; exact fixed688-byte reply carrier'}
def baseline():
 b=inherited.inherited.compose(inherited.inherited.baseline(),read(inherited.inherited.E/'NFD_LEDGER_DELTA.json'))
 inherited.packet_check(read(inherited.E/'NFH_LEDGER_DELTA.json'));inherited.artifacts()
 return b

@lru_cache(maxsize=1)
def checked_supports():
 from NFD_scan_checks import audit
 audit()
 return all_native()

def certificate(c,base):
 try:
  assert c['subject']==F and c['id']=='NFJ_scanner' and c['kind']=='root-composition' and c['frozen_revision']==REV==base['frozen_revision']
  assert c['semantic_review_sha256']==sha(json.dumps({k:v for k,v in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  assert c['inner_hypotheses_remaining']==[] and c['hypotheses']==HYPOTHESES
  assert c['trust_classification']=='P6/D188 option A reclassification; uses RuntimeMemcmp (ac), ADDED trust'
  assert c['new_trust_rows']==[TRUST] and c['runtime_contract']=='RuntimeMemcmp688Zero'
  assert all(c[k] is True for k in FLAGS)
  assert c['source_association']==checked_supports() # all original gates, unchanged inputs checked once per process
  assert [t['name'] for t in c['domain_theorems']]==NAMES and c['physical_theorems']==c['domain_theorems']
  import NED_validate
  for t in c['domain_theorems']:NED_validate.theorem(t)
  assert c['native_certificate']==dict(complete=True,domain='all valid immutable slices, arbitrary raw bytes and length; all Result and rejection paths',positive=['NFJ_K003','NFJ_K011','NFJ_K013'],controls=[f'NFJ_K{n:03}' for n in [4,5,6,7,8,9,10,12,14]],inherited='NFD_K134..150; no root credit from supports alone',no_writable_static=True,no_function_pointer=True)
  by={}
  for r in base['rows']:by.setdefault(r['function'],[]).append(r)
  row=by[F][0]
  assert c['required_obligations']==[o['id'] for o in row['caller_domain_obligations']]
  assert c['primitive_certificates']==PRIMITIVES
  edges={F+' -> '+g for g in row['canonical_callees']}
  assert set(c['edges'])==set(c['call_domain_certificates'])==edges and len(edges)==3
  for edge,d in c['call_domain_certificates'].items():
   g=edge.split(' -> ')[1]
   assert all(r['composed_status']=='CLOSED' for r in by[g])
   assert d['subject']==edge and d['classification']==CLASSIFICATIONS[g]
   names={h['name'] for r in by[g] for h in r['named_hypotheses']}|{h for o in row['caller_domain_obligations'] if o.get('callee')==g for h in o['required_named_hypotheses']}
   assert set(d['inner_names_discharged'])==names and d['inner_hypotheses_remaining']==[]
   assert set(d['selected_callee_claims'])=={x for r in by[g] for x in r['selected_claims']}
   assert d['domain_theorems']==c['domain_theorems'] and d['physical_theorems']==c['physical_theorems'] and all(d[k] is True for k in FLAGS)
  assert c['runtime_domain']==dict(left='SAME retained successful encoder reply allocation',right='SAME retained header allocation bytes[0..688]',left_length=688,right_length=688,length_argument=688,reply='SAME supplied local i32 slot',observation='zero only',other_slot_observers=[],equal_continuation='frozen tag test and same candidate/proof_length return',unequal_continuation='frozen InvalidAccountData',completion='NFH_ComparisonDomain.complete688_association/complete688_on_domain')
  for pin in c['support']:assert sha((R/pin['path']).read_bytes())==pin['sha256']
  assert {p['path'] for p in c['support']}==support_paths()
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError,ImportError):return False

def support_paths():
 names=['NFJ_NATIVE.md','NFJ_Comparison.lean','NFJ_Scanner.lean','NFJ_kani_gate.py','NFJ_native.py','NFJ_source_checks.py','NFJ_FROZEN_INPUT.json.xz','NFJ_FROZEN_INPUT.json.sha256','NFJ_INCLUDES.json','NFJ_FROZEN_GRAPH.json','NFJ_contract_controls.patch','NFJ_KMX_copy_stubs.patch']
 for n in range(3,15):
  a=f'NFJ_K{n:03}'
  names += [a+'/'+s for s in ['receipt.json','stdout.log','time.log']]+[a+s for s in ['.json','-shape.json','-NFJ_native.patch','-admission.json','-graph-check.json','-lock-check.json','-source-check.json','-rule16-check.json','-frozen-identity.json','-metadata-pin.json']]
 return {str((E/n).relative_to(R)) for n in names}

def compose(base,packet):
 assert packet['inherits']=='evidence/slice-s-compose11-20261104/NFH_LEDGER_DELTA.json'
 out=copy.deepcopy(base);c=packet.get('NFJ_certificates',{}).get(F)
 if not c or not certificate(c,base):return out
 out['trust_rows'].append(TRUST)
 for r in out['rows']:
  if r['function']!=F:continue
  r.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',composed_reason='NFJ exact same-call hybrid scanner certificate; uses RuntimeMemcmp (ac), ADDED trust',selected_claims=['NFJ::'+F],open_transitive_dependencies=[])
  r['claim_ids']=list(dict.fromkeys(r['claim_ids']+['NFJ::'+F]))
  r['trust_rows']=list(r['trust_rows'])+['RuntimeMemcmp']
  r['named_hypotheses']=[dict(name=n,statement=n,discharged_by=c['id']+'::'+n) for n in HYPOTHESES]
  for o in r['caller_domain_obligations']:
   if 'callee' in o:
    d=c['call_domain_certificates'][F+' -> '+o['callee']]
    o['callee_claims']=list(dict.fromkeys(o['callee_claims']+d['selected_callee_claims']))
    o['required_named_hypotheses']=list(dict.fromkeys(o['required_named_hypotheses']+d['inner_names_discharged']))
   o.update(status='CLOSED',discharged_by=c['id']+'::'+o['id'])
 return out

def main(base=None):
 if base is None:base=baseline()
 packet=read(E/'NFJ_LEDGER_DELTA.json');out=compose(base,packet)
 summary=__import__('NEU_validate').summary(out)
 # Full inherited baseline is replayed on this run, never treated as a flag.
 assert certificate(packet['NFJ_certificates'][F],base)
 spec=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
 ids={r['row']:r for r in out['rows']};edge_out=[]
 for edge in spec['internal_edges']:
  f,g=edge.split(' -> ');rs=[r for r in out['rows'] if r['function']==f]
  obligations=[o for r in rs for o in r['caller_domain_obligations'] if o.get('callee')==g]
  edge_out.append(dict(edge=edge,status='CLOSED' if obligations and all(o['status']=='CLOSED' for o in obligations) else 'OPEN'))
 rows=[r for r in out['rows'] if r['function'] in spec['functions']]
 result=dict(closed_rows=sum(r['composed_status']=='CLOSED' for r in rows),total_rows=len(rows),closed_edges=sum(e['status']=='CLOSED' for e in edge_out),total_edges=len(edge_out),closed_roots=sum(all(r['composed_status']=='CLOSED' for r in rows if r['function']==f) for f in spec['roots']),total_roots=len(spec['roots']),uses='uses RuntimeMemcmp (ac), ADDED trust',owner_confirmation='pending',target='not yet established',summary=summary)
 (E/'NFJ_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');(E/'NFJ_EDGES.json').write_text(json.dumps(edge_out,indent=1)+'\n')
 (E/'NFJ_CHECKED_ROWS.json').write_text(json.dumps(rows,indent=1)+'\n');(E/'NFJ_BASELINE_ROWS.json').write_text(json.dumps([r for r in base['rows'] if r['function'] in spec['functions']],indent=1)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='summary'},indent=1))
if __name__=='__main__':main()
