"""Source-ordered actual wrapper cut, plain proof, local ghost observation only.
The child oracle produces every typed Result; it writes no static or account.
Source erasure restores the complete frozen wrapper body byte-for-byte.
"""
from NKP_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
# Retain the predecessor's value constructors exactly, with provenance/hash.
old=E.parent/'tx2-adapters-20261108/NKF_wrappers.py'
import ast
module_ast=ast.parse(old.read_text());COMMON=next(ast.literal_eval(n.value) for n in module_ast.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
FIELDS={'master':['a.bump==b.bump','a.identity.pool[j]==b.identity.pool[j]','a.identity.asset_mint[j]==b.identity.asset_mint[j]','a.identity.token_program[j]==b.identity.token_program[j]','a.identity.asset_id.0==b.identity.asset_id.0','a.identity.deployment_domain[j]==b.identity.deployment_domain[j]','a.verifier_policy.flags==b.verifier_policy.flags','a.verifier_policy.registry_program[j]==b.verifier_policy.registry_program[j]','a.verifier_policy.registry_authority[j]==b.verifier_policy.registry_authority[j]','a.verifier_policy.policy_binding[j]==b.verifier_policy.policy_binding[j]','a.initialized_lane_mask==b.initialized_lane_mask','a.has_checkpoint==b.has_checkpoint','a.next_checkpoint_sequence==b.next_checkpoint_sequence','a.last_checkpoint_lane_sequences[j%8]==b.last_checkpoint_lane_sequences[j%8]'], 'checkpoint':['a.bump==b.bump','a.master[j]==b.master[j]','a.deployment_domain[j]==b.deployment_domain[j]','a.checkpoint_sequence==b.checkpoint_sequence','a.global_root[j%8].0==b.global_root[j%8].0','a.lane_sequences[j%8]==b.lane_sequences[j%8]']}
def shape(kind,field,mode):
 typ='PoolV1PairForest'+kind.title()+'V1';name='decode_'+kind+'_box';child='decode_pool_v1_pair_forest_'+kind+'_v1';mod='NKP_'+kind+'_tail'
 frozen=json.loads((E.parent/'tx2-adapters-20261108'/('NKF_'+kind+'_SOURCE.json')).read_text())['frozen_body']
 compare=FIELDS[kind][field] if field>=0 else 'true'
 lhs=compare.split('==')[0].replace('a.','b.')
 mutate=lhs+' ^= 1;'
 if kind=='master' and field==11:mutate=lhs+' = !'+lhs+';'
 corrupt=('kani::assume(raw.is_ok());if let Ok(ref mut b)=out{'+mutate+'}') if mode=='inverse' and field>=0 else 'kani::assume(raw.is_err());' if mode=='inverse' else ''
 instrumented=f'''fn {name}(bytes: &[u8]) -> Result<Box<{typ}>, ProgramError> {{
    let raw = {child}(bytes);
    let mut out = (|| {{ Ok(Box::new(raw.map_err(|_| ProgramError::InvalidAccountData)?)) }})();
    #[cfg(kani)] {{
        let j:usize=kani::any();kani::assume(j<32);
        {corrupt}
        let good=match (&raw,&out) {{(Ok(a),Ok(b))=>{compare},(Err(_),Err(e))=>*e==ProgramError::InvalidAccountData,_=>false}};
        assert!({'!good' if mode=='inverse' and field<0 else 'good'}, "actual wrapper returned field/error at SAME raw decoder call");
    }}
    out
}}'''
 text=COMMON+f'''
fn raw_oracle(_bytes:&[u8])->Result<{typ},F>{{if kani::any(){{Ok(any_{kind}())}}else{{Err(any_error())}}}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(aspis_statement::pool_v1::{child},raw_oracle)]
fn returned(){{let bytes:[u8;33]=kani::any();let length:usize=kani::any();kani::assume(length<=33);let _={name}(&bytes[..length]);}}
'''
 return text,[(frozen,instrumented)],mod
if __name__=='__main__':
 import sys
 a,kind,field,mode=sys.argv[1:];text,edits,mod=shape(kind,int(field),mode)
 patch='--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True))
 (E/(a+'.patch')).write_text(patch)
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,kind=kind,field=int(field),mode=mode,oracle='full arbitrary typed child Result at unchanged bytes',modifies=[],edits=edits,instrumented_sha256=sha(edits[0][1].encode()),reference='raw = actual source child invocation at SAME immutable bytes',input_length='0..33 native representative; body tail never reads bytes, source child argument unchanged'),indent=1)+'\n')
 submit(a,'r1_pool_adapter::'+mod+'::returned',P,mod,text,mode,edits=edits)
