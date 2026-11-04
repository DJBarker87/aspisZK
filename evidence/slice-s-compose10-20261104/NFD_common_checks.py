"""Common constructor admission: same actual native types and complete AA Box value."""
import re,json,subprocess
import NFD_validate as v
import NFD_bridge_checks as root
from NFD_native_checks import native
E=v.E;R=v.R
COMMON='programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common'
FIELDS=['master_account[j]','checkpoint_account[j]','selected_lane_account[j]','output_lane','checkpoint_sequence','historical_global_anchor[i].0','lane_transition.live_snapshot.pool[j]','lane_transition.live_snapshot.deployment_domain[j]','lane_transition.live_snapshot.sequence','lane_transition.live_snapshot.next_pair_index','lane_transition.live_snapshot.current_root[i].0','lane_transition.live_snapshot.frontier[k][i].0','lane_transition.candidate_afterstate.next_pair_index','lane_transition.candidate_afterstate.next_root[i].0','lane_transition.candidate_afterstate.next_frontier[k][i].0']
RHS=['a.master_account[j]','a.checkpoint_account[j]','a.selected_lane_account[j]','a.selected_lane.lane_id','a.checkpoint.checkpoint_sequence','a.checkpoint.global_root[i].0','a.live_snapshot.pool[j]','a.live_snapshot.deployment_domain[j]','a.live_snapshot.sequence','a.live_snapshot.next_pair_index','a.live_snapshot.current_root[i].0','a.live_snapshot.frontier[k][i].0','c.next_pair_index','c.next_root[i].0','c.next_frontier[k][i].0']
THEOREMS=['NEU_ReconstructCore.common_result','NEU_CallDomains.common_packet','NEU_CommonProjections.common_ext']+[f'NFD_CommonField{i:02}.alignment' for i in range(15)]
def added(patch):
 frag=patch.split('+++ b/programs/r1-cost-probe/src/NFD_reconstruct.rs\n',1)[1].split('--- a/',1)[0]
 return '\n'.join(l[1:] for l in frag.splitlines() if l.startswith('+'))+'\n'
def source(slot,mode):
 t=v.read(E/'NFD_COMMON_TEMPLATE.json');assert v.sha(t['source'].encode())==t['source_sha256']=='66a2bad5d671b27dd89b1390794e1f3943a5512e723e95c1399853021afee60a'
 s=t['source'].replace('0=>out.master_account[j] as u64','0=>out.'+FIELDS[slot]+' as u64').replace('0=>a.master_account[j] as u64','0=>'+RHS[slot]+' as u64'+('^1' if mode=='negative' else ''))
 if mode=='wrong_allocation':s=s.replace('    out\n}', '    Box::new(*out)\n}')
 return s

def attempt(a,slot,mode):
 snap=native(a,mode=='positive');m=v.read(E/(a+'-shape.json'))
 assert m['shape']=='common_actual' and m['mode']==mode and m['field_slot']==slot
 assert m['all_fields']==[[l,r] for l,r in zip(FIELDS,RHS)]
 assert v.read(E/(a+'.json'))['module']=='r1_pool_adapter::NFD_reconstruct::reconstruction_slice'
 text=added(snap['NFD_native_contracts.patch']);assert text==source(slot,mode)
 frozen=subprocess.check_output(['git','show',root.REV+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
 start=frozen.index('fn asq8_common(');original=frozen[start:frozen.index('\n}',start)+2];assert m['frozen_body']==original
 restored=m['native'].replace('fn native(','fn asq8_common(').replace('f:&mut Frame) ->',') ->').replace('    let out=Box::new(','    Box::new(').replace('    });\n    f.allocated=&*out;\n    out\n}','    })\n}')
 if mode=='wrong_allocation':restored=restored.replace('    });\n    f.allocated=&*out;\n    Box::new(*out)\n}','    })\n}')
 assert restored==original
 assert 'safe typed arbitrary constructors' in v.read(E/'NFD_AUTH_INITIALIZATION.json')['method']
 # The immutable template includes direct independent arbitrary constructors of
 # every actual field: no fixed unread fields and no byte havoc/fabricated values.
 assert 'fn auth()->Box<AuthenticatedAsq8Accounts>{Box::new(AuthenticatedAsq8Accounts{' in text
 assert all(token not in text for token in ['unsafe{','transmute','static mut','stub_verified','let mut a=Box::new'])
 assert 'assert!(core::ptr::eq(out.as_ref(),frame.allocated))' in text
 assert re.findall(r'kani::assume\((.*?)\)',text)==['i<8&&j<32&&k<20&&selector<1']
 return True

def check(c,base):
 assert c['subject']==COMMON and c['kind']=='member-composition'
 assert c['native_certificate']['function']==COMMON and c['native_certificate']['complete'] is True
 assert c['hypotheses']==[COMMON+'.PacketDomain',COMMON+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'] and c['new_trust_rows']==[]
 assert c['edges']==[] and c['call_domain_certificates']=={}
 assert [t['name'] for t in c['domain_theorems']]==THEOREMS and c['physical_theorems']==c['domain_theorems']
 n=c['native_certificate'];assert n['domain']=='every typed Auth/Candidate with every scalar independently arbitrary; no canonicality or accepted-run restriction'
 assert n['pairs']==[[f'NFD_K{38+2*i:03}',f'NFD_K{39+2*i:03}'] for i in range(15)] and n['controls']==['NFD_K068']
 for slot,pair in enumerate(n['pairs']):
  for a,mode in zip(pair,['positive','negative']):attempt(a,slot,mode)
 attempt('NFD_K068',0,'wrong_allocation')
 expected=[o['id'] for r in base['rows'] if r['function']==COMMON for o in r['caller_domain_obligations']];assert c['required_obligations']==expected
 assert all(o['call']['name'] in ['new'] for r in base['rows'] if r['function']==COMMON for o in r['caller_domain_obligations'])
 paths={str((E/name).relative_to(R)) for name in ['NFD_COMMON_TEMPLATE.json','NFD_AUTH_INITIALIZATION.json']}
 for a in [a for pair in n['pairs'] for a in pair]+n['controls']:
  names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NFD_native_contracts.patch',a+'-NFD_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NFD_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256']
  paths.update(str((E/name).relative_to(R)) for name in names)
 assert {ref['path'] for ref in c['support']}==paths
 return True
