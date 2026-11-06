from NKP_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
def harness(kind,field,mode):
 size=192 if kind=='checkpoint' else 384
 fields={'checkpoint':['a.bump==b.bump','a.master[j]==b.master[j]','a.deployment_domain[j]==b.deployment_domain[j]','a.checkpoint_sequence==b.checkpoint_sequence','a.global_root[j%8].0==b.global_root[j%8].0','a.lane_sequences[j%8]==b.lane_sequences[j%8]'], 'master':['a.bump==b.bump','a.identity.pool[j]==b.identity.pool[j]','a.identity.asset_mint[j]==b.identity.asset_mint[j]','a.identity.token_program[j]==b.identity.token_program[j]','a.identity.asset_id.0==b.identity.asset_id.0','a.identity.deployment_domain[j]==b.identity.deployment_domain[j]','a.verifier_policy.flags==b.verifier_policy.flags','a.verifier_policy.registry_program[j]==b.verifier_policy.registry_program[j]','a.verifier_policy.registry_authority[j]==b.verifier_policy.registry_authority[j]','a.verifier_policy.policy_binding[j]==b.verifier_policy.policy_binding[j]','a.initialized_lane_mask==b.initialized_lane_mask','a.has_checkpoint==b.has_checkpoint','a.next_checkpoint_sequence==b.next_checkpoint_sequence','a.last_checkpoint_lane_sequences[j%8]==b.last_checkpoint_lane_sequences[j%8]']}[kind]
 compare=fields[field] if field>=0 else 'true'
 lhs=compare.split('==')[0].replace('a.','b.');mutate=lhs+' = !'+lhs+';' if not lhs.endswith('.has_checkpoint') else lhs+' = !'+lhs+';'
 if field>=0 and kind=='master' and field==4:mutate='b.identity.asset_id.0 ^= 1;'
 elif field>=0 and ((kind=='checkpoint' and field==4)):mutate='b.global_root[j%8].0 ^= 1;'
 elif field>=0 and not (kind=='master' and field==11):mutate=lhs+' ^= 1;'
 corrupt='kani::assume(raw.is_ok());if let Ok(ref mut b)=out{'+mutate+'}' if mode=='inverse' and field>=0 else ''
 # The SAME bytes are read through both immutable calls. No Result<Box> contract.
 text='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n#[kani::proof] #[kani::unwind(400)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn returned(){\n let bytes:[u8;SIZE]=kani::any();let length:usize=kani::any();kani::assume(length<=SIZE);\n let j:usize=kani::any();kani::assume(j<32);\n let raw=decode_pool_v1_pair_forest_KIND_v1(&bytes[..length]);\n let mut out=decode_KIND_box(&bytes[..length]);\n CORRUPT
 let good=match (raw,out){(Ok(a),Ok(b))=>COMPARE,(Err(_),Err(e))=>e==ProgramError::InvalidAccountData,_=>false};\n assert!(VERDICT,"SAME-byte returned Box field/error");\n}\n'.replace('SIZE',str(size)).replace('KIND',kind).replace('COMPARE',compare).replace('VERDICT','!good' if mode=='inverse' and field<0 else 'good').replace('CORRUPT',corrupt)
 return text
if __name__=='__main__':
 import sys
 a,kind,field,mode=sys.argv[1:];text=harness(kind,int(field),mode);module='NKP_'+kind+'_box'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+module+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 submit(a,'r1_pool_adapter::'+module+'::returned',P,module,text,mode)
