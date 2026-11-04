"""Strict new native/Lean shapes; inherited certificates are never modified."""
import re,json,difflib,copy,subprocess
from pathlib import Path
import NFD_validate as v
from NFD_native_checks import native
from NFD_source_checks import request_reference,frozen_body,REV,P
E=v.E;R=v.R
REQUEST=P+'::decode_pool_v1_pair_forest_terminal_request_v1'
SPEC=v.read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
FLAGS=['same_arguments','same_prestate','same_result','same_ordered_effects','canonical_carrier','callee_domain_established','native_frame_complete']
THEOREMS=['NFD_RequestOracle.array_result_state_effects','NFD_RequestOracle.result_state_effects','NFD_RequestDomains.wrong_length','NFD_RequestDomains.payment_length','NFD_RequestDomains.binding_fields','NFD_RequestDomains.payment_window','NFD_RequestProjection.transfer_roundtrip','NFD_RequestProjection.withdrawal_roundtrip','NFD_RequestProjection.complete']+[f'NFD_RequestField{i:02}.alignment' for i in range(14)]

def projections():
 common=['pool[j]','deployment_domain[j]','anchor_sequence','anchor_root[i].0','nullifier[i].0','asset_id.0','change_commitment[i].0']
 out=['match p{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)=>1,PoolV1PairForestTerminalPaymentV1::Withdrawal(_)=>2}']
 for f in common:out.append('match p{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p.'+f+' as u64,PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>p.'+f+' as u64}')
 for ty,f in [('PrivateTransfer','recipient_commitment[i].0'),('Withdrawal','amount'),('Withdrawal','destination_token_account[j]')]:out.append('match p{PoolV1PairForestTerminalPaymentV1::'+ty+'(p)=>p.'+f+' as u64,_=>0}')
 return out

def source(slot,mode):
 t=v.read(E/'NFD_REQUEST_TEMPLATE.json');assert v.sha(t['source'].encode())==t['source_sha256']=='628c450e010c6938e1cf60ea7749408247524d0d987cdad72381421c4fcc1a17'
 s=t['source'];ps=projections();p=lambda ex:'fn project(p:&PoolV1PairForestTerminalPaymentV1,i:usize,j:usize)->u64{'+ex+'}'
 s=s.replace(p(ps[0]),p(ps[0 if slot<3 else slot-3]))
 obs=['r.verifier_profile[j] as u64','r.verifier_release[j] as u64','r.pool_program[j] as u64','project(&r.public,i,j)'][min(slot,3)]
 ex=['bytes[8+j] as u64','bytes[40+j] as u64','bytes[72+j] as u64','f.observed'][min(slot,3)]
 s=s.replace('assert!(r.verifier_profile[j] as u64==bytes[8+j] as u64);','assert!('+obs+'=='+ex+('^1' if mode=='value' else '')+');')
 if mode=='argument':s=s.replace('bytes[REQUEST_PAYMENT_OFFSET..]','bytes[REQUEST_PAYMENT_OFFSET+1..]')
 if mode=='value' and slot>=11:s=s.replace('let i:usize=kani::any();','kani::assume(bytes[5]=='+('1' if slot==11 else '2')+');let i:usize=kani::any();')
 return s

def attempt(a,slot,mode):
 m=v.read(E/(a+'-shape.json'));snap=native(a,mode=='positive');c=v.read(E/(a+'.json'))
 assert c['module']=='pool_v1::pair_forest_terminal::NFD_request::request'
 assert m['mode']==mode and m['field_slot']==slot
 assert m['source']==source(slot,mode)
 f=subprocess.check_output(['git','show',REV+':'+P],text=True);original=frozen_body(f,REQUEST.rsplit('::',1)[1]);assert original==m['frozen_body']
 restored=m['native'].replace('fn native(','pub fn decode_pool_v1_pair_forest_terminal_request_v1(').replace('    bytes: &[u8],f:&mut Frame,','    bytes: &[u8],')
 from NEY_bridge_checks import undo
 restored=undo(restored,'transfer','decode_pool_v1_private_transfer_public_v1');restored=undo(restored,'withdrawal','decode_pool_v1_withdrawal_public_v1')
 if mode=='argument':restored=restored.replace('REQUEST_PAYMENT_OFFSET+1','REQUEST_PAYMENT_OFFSET')
 assert restored==original
 name='NFD_request';hook=f+'\n#[cfg(kani)]\n#[path="'+name+'.rs"]\nmod '+name+';\n'
 patch=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+P,tofile='b/'+P))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/'+name+'.rs\n@@ -0,0 +1,'+str(len(m['source'].splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in m['source'].splitlines())
 assert snap['NFD_native_contracts.patch']==patch
 if mode!='positive':
  log=(E/a/'stdout.log').read_text();assert 'Failed Checks: assertion failed:' in log
  assert (' ^ 1' in log) if mode=='value' else ('bytes.len() == 216' in log)
 return True

def request(c):
 n=c['native_certificate'];assert n['domain']=='all valid immutable slices; every raw byte and error path; no canonicality restriction'
 assert n['pairs']==[[f'NFD_K{3+2*i:03}',f'NFD_K{4+2*i:03}' if i!=11 else 'NFD_K034'] for i in range(14)]
 for slot,pair in enumerate(n['pairs']):
  for a,mode in zip(pair,['positive','value']):attempt(a,slot,mode)
 assert n['controls']==['NFD_K033'];attempt('NFD_K033',0,'argument')
 assert n['length_partition']==['NFD_K031','NFD_K032']
 for a,positive in zip(n['length_partition'],[True,False]):
  snap=native(a,positive);m=v.read(E/(a+'-shape.json'))
  assert m['mode']==('positive' if positive else 'value')
  assert 'let bytes_len:usize=kani::any();' in m['source']
  assert 'actual=='+('' if positive else '!')+'(bytes_len!=320)' in m['source']
  assert m['source'] in ''.join(l[1:]+'\n' for l in snap['NFD_native_contracts.patch'].splitlines() if l.startswith('+') and not l.startswith('+++'))
 assert c['reference_source']==request_reference()
 return True

def request_check(c,base):
 assert c['subject']==REQUEST and c['kind']=='root-composition'
 assert c['native_certificate']['function']==REQUEST and c['native_certificate']['complete'] is True
 assert c['hypotheses']==[REQUEST+'.PacketDomain',REQUEST+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA']
 assert c['new_trust_rows']==[]
 assert [t['name'] for t in c['domain_theorems']]==THEOREMS and c['physical_theorems']==c['domain_theorems']
 request(c)
 by={}
 for r in base['rows']:by.setdefault(r['function'],[]).append(r)
 assert c['required_obligations']==[o['id'] for r in by[REQUEST] for o in r['caller_domain_obligations']]
 edges={e for e in SPEC['internal_edges'] if e.startswith(REQUEST+' -> ')}
 assert set(c['edges'])==set(c['call_domain_certificates'])==edges
 for edge,d in c['call_domain_certificates'].items():
  g=edge.split(' -> ')[1];assert d['subject']==edge
  assert d['classification']==('native U8 discriminator1/2, exact emitted enum carrier' if g.endswith('::transition_kind') else 'same immutable216-byte suffix; all-raw decoder domain; exact returned record/error carrier')
  names={h['name'] for r in by[g] for h in r['named_hypotheses']}|{h for r in by[REQUEST] for o in r['caller_domain_obligations'] if o.get('callee')==g for h in o['required_named_hypotheses']}
  assert set(d['inner_names_discharged'])==names and d['inner_hypotheses_remaining']==[]
  assert set(d['selected_callee_claims'])=={x for r in by[g] for x in r['selected_claims']} and d['selected_callee_claims']
  assert d['domain_theorems']==c['domain_theorems'] and d['physical_theorems']==c['physical_theorems']
  assert all(d[k] is True for k in FLAGS)
 # Full support set: no missing receipt, body, graph/feature/lock or source snapshot.
 attempts=[a for pair in c['native_certificate']['pairs'] for a in pair]+c['native_certificate']['controls']+c['native_certificate']['length_partition']
 paths={str((E/'NFD_REQUEST_TEMPLATE.json').relative_to(R)),str((E/'NFD_REQUEST_REFERENCE.json').relative_to(R))}
 for a in attempts:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NFD_native_contracts.patch',a+'-NFD_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NFD_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256']
  paths.update(str((E/name).relative_to(R)) for name in names)
 assert {ref['path'] for ref in c['support']}==paths
 return True

def check(c,base):
 if c['subject']==REQUEST:return request_check(c,base)
 from NFD_common_checks import COMMON,check as common_check
 if c['subject']==COMMON:return common_check(c,base)
 from NFD_reconstruction_checks import F,check as reconstruct_check
 if c['subject']==F:return reconstruct_check(c,base)
 from NFD_emit_checks import F as EMIT,check as emit_check
 if c['subject']==EMIT:return emit_check(c,base)
 from NFD_raw_checks import LIMBS,TAG,check as raw_check
 if c['subject'] in [LIMBS,TAG]:return raw_check(c,base)
 from NFD_wide_checks import F as WIDE,check as wide_check
 if c['subject']==WIDE:return wide_check(c,base)
 return False

def compose_additions(base,result,packet,api):
 by={}
 for r in result['rows']:by.setdefault(r['function'],[]).append(r)
 for f,c in packet.get('NFD_certificates',{}).items():
  if not api.certificate(c,f,result):continue
  # Only the exact, independently validated WideExact u32 method-resolution
  # certificate may remove conservative M31/self alternatives.
  noncalls=c.get('resolved_non_calls',{})
  if noncalls:
   from NFD_wide_checks import F as WIDE,RESOLVED
   assert f==WIDE and noncalls==RESOLVED
  if any(any(r['composed_status']!='CLOSED' for r in by[g]) for g in by[f][0]['canonical_callees'] if g not in noncalls):continue
  for r in by[f]:
   r.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=['NFD::'+f])
   r['claim_ids']=list(dict.fromkeys(r['claim_ids']+['NFD::'+f]))
   for name in [f+'.PacketDomain',f+'.PhysicalInterpretation']:
    if name not in {h['name'] for h in r['named_hypotheses']}:r['named_hypotheses'].append(dict(name=name,statement=(c['native_certificate'].get('domain','Root-owned full immutable slice / exact native-cohort typed carrier') if name.endswith('.PacketDomain') else 'Root-owned valid native/cohort typed carrier, ABI and approved library/allocator interpretation'),discharged_by=c['id']+'::'+name))
   for h in r['named_hypotheses']:h['discharged_by']=c['id']+'::'+h['name']
   for o in r['caller_domain_obligations']:
    if 'callee' in o and o['callee'] not in noncalls:
     d=c['call_domain_certificates'][f+' -> '+o['callee']];o['callee_claims']=list(dict.fromkeys(o['callee_claims']+d['selected_callee_claims']));o['required_named_hypotheses']=list(dict.fromkeys(o['required_named_hypotheses']+d['inner_names_discharged']))
    o.update(status='CLOSED',discharged_by=c['id']+'::'+o['id'])
   if noncalls:
    r['resolved_non_calls']=noncalls
    r['canonical_callees']=[g for g in r['canonical_callees'] if g not in noncalls]
   r['open_transitive_dependencies']=[g for g in r['open_transitive_dependencies'] if g not in noncalls and any(x['composed_status']!='CLOSED' for x in by[g])]
   if not r['open_transitive_dependencies']:r.update(composed_status='CLOSED',composed_reason='NFD full-field native request, exact frozen reference continuation, full carrier/domain and complete Result/order certificates; option A reclassification')
 return result
