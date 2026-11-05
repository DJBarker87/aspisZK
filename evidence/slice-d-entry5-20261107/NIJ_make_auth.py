"""Exact comparison cuts from frozen authentication, local logs and no hidden success."""
from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';S='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
src=subprocess.check_output(['git','show',F+':'+S],text=True);auth=src[src.index('fn authenticate_invariant_release_registry('):src.index('fn authenticate_asq8_accounts(')]
conditions=re.findall(r'if ((?:registry|entry)\.pool !=.*?)(?:\n        |\n    )\{',auth,re.S);assert len(conditions)==4,len(conditions)
x=json.loads((E/'NIJ_NATIVE_INPUTS.json').read_text());old=x['programs/r1-cost-probe/src/NHY_auth.rs']
s='''use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct Log{count:u8,slots:[u8;16]}
fn mark(log:&mut Log,index:u8,value:bool)->bool{log.slots[log.count as usize]=index;log.count+=1;value}
'''
for name in ['registry1','registry2','entry1','entry2','arbitrary_status']:
 line=next(l for l in old.splitlines() if l.startswith('fn '+name+'('));s+=line+'\n'
s+='fn policy()->aspis_statement::pool_v1::VerifierPolicyV1{aspis_statement::pool_v1::VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()}}\n'
rows=[]
for idx,cond in enumerate(conditions):
 name=['registry_v2','entry_v2','registry_v1','entry_v1'][idx];ty=['VerifierRegistryV2','VerifierRegistryEntryV2','VerifierRegistryV1','VerifierRegistryEntryV1'][idx];param='registry' if name.startswith('registry') else 'entry'
 cond=cond.replace('master_account.key()','master_key').replace('master.verifier_policy','policy')
 guards=[g.strip() for g in cond.split('||')];ng=len(guards)
 wrapped=' || '.join(f'mark(&mut log,{i},({g}))' for i,g in enumerate(guards))
 signature=f'{param}:&aspis_statement::pool_v1::{ty},policy:&aspis_statement::pool_v1::VerifierPolicyV1,master_key:&Pubkey,registry_program:&Pubkey,loader:&Pubkey,registry_programdata:&Pubkey,verifier_program:&Pubkey,verifier_programdata:&Pubkey,current_slot:u64,j:usize'
 for suffix,bad in [('',False),('_wrong',True)]:
  n=name+suffix
  s+=f'''fn {n}_packet({signature}){{
 kani::assume(j<16);
 let mut log=Log{{count:0,slots:[255;16]}};
 let result=(||->ProgramResult{{if {wrapped} {{return Err(ProgramError::InvalidAccountData);}}Ok(())}})();
 let flags=[{','.join('('+g+')' for g in guards)}];
 let first='''+''.join(f'if flags[{i}]{{{i}}}else{{' for i in range(ng))+str(ng)+'}'*ng+f''';
 let expected_count=if first=={ng}{{{ng}}}else{{first+1}};
 let value=if first=={ng}{{matches!(result,Ok(()))}}else{{matches!(result,Err(ProgramError::InvalidAccountData))}};
 let good=value&&log.count as usize==expected_count&&log.slots[j]==if j<expected_count{{j as u8}}else{{255}};
 assert!({'!' if bad else ''}good);
}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{{n}_packet(&{['registry2','entry2','registry1','entry1'][idx]}(),&policy(),&Pubkey::new_from_array(kani::any()),&Pubkey::new_from_array(kani::any()),&Pubkey::new_from_array(kani::any()),&Pubkey::new_from_array(kani::any()),&Pubkey::new_from_array(kani::any()),&Pubkey::new_from_array(kani::any()),kani::any(),kani::any());}}
'''
 rows.append(dict(name=name,original_condition=conditions[idx],condition=cond,guards=guards,guard_count=ng,source_projection_replacements={'master_account.key()':'master_key','master.verifier_policy':'policy'},status='support only until entire decoder/PDA/authentication chain'))
p='programs/r1-cost-probe/src/NIJ_auth.rs';x[p]=s;q=S;suffix='\n#[cfg(kani)]\n#[path="NIJ_auth.rs"]\nmod NIJ_auth;\n';assert suffix not in x[q];x[q]+=suffix
(E/'NIJ_NATIVE_INPUTS.json').write_text(json.dumps(x));(E/'NIJ_auth.rs.txt').write_text(s);pins=json.loads((E/'NIJ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NIJ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1))
(E/'NIJ_AUTH_CUTS.json').write_text(json.dumps(dict(frozen_revision=F,source=S,source_sha256=hashlib.sha256(src.encode()).hexdigest(),cuts=rows,source_erasure='Remove mark(log,i,guard) wrappers and project supplied master_key/policy back to source receivers; exact frozen comparison order. No branch restriction; every full typed record/status/slot and independent key admitted.'),indent=1)+'\n')
