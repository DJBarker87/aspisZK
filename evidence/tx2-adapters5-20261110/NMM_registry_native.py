from NMM_native import *
import ast
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
PIN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def function(s,name):
 a=s.index('fn '+name+'(');b=s.index('{',a);i=b+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
def common():
 path='evidence/tx2-adapters-20261108/NKF_wrappers.py'
 text=subprocess.check_output(['git','show','HEAD:'+path],text=True)
 tree=ast.parse(text)
 value=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='COMMON' for x in n.targets))
 (E/'NMM_REGISTRY_CTOR_PROVENANCE.json').write_text(json.dumps(dict(source=path,sha256=sha(text.encode()),validated=False,scope='Unrestricted typed Master constructor only; no predecessor native credit inherited'),indent=2)+'\n')
 fmt=subprocess.check_output(['git','show',PIN+':crates/aspis-statement/src/pool_v1/format.rs'],text=True)
 policy=function(fmt,'validate_verifier_policy_v1').replace('fn validate_verifier_policy_v1(', 'fn NMM_policy_reference(',1)
 pool= subprocess.check_output(['git','show',PIN+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
 ids='\n'.join(function(pool,n).replace('fn '+n+'(', 'fn NMM_'+n+'_reference(',1) for n in ['pool_program_id','registry_program_id'])
 return value+'\nuse aspis_statement::pool_v1::*;\n'+policy+'\n'+ids
HELP='''
fn NMM_pool_cut()->[u8;32] {let out:[u8;32]=kani::any();kani::assume(out==NMM_pool_program_id_reference());out;out}
fn NMM_registry_id_cut()->[u8;32] {let out:[u8;32]=kani::any();kani::assume(out==NMM_registry_program_id_reference());out}
fn NMM_policy_cut(p:&VerifierPolicyV1)->Result<(),PoolV1FormatError> {
 let expected=NMM_policy_reference(p);let tag:u8=kani::any();kani::assume(tag<4);
 let out=match tag {0=>Ok(()),1=>Err(PoolV1FormatError::UnsupportedFlags),2=>Err(PoolV1FormatError::ZeroRequiredBinding),_=>Err(PoolV1FormatError::InvalidAuthorityMode)};
 kani::assume(out==expected);out
}
fn NMM_readonly_reference(a:&OwnedAccount,p:&Pubkey)->ProgramResult {
 if a.owner!=*p||a.is_signer||a.is_writable||a.executable {Err(ProgramError::InvalidAccountData)}else{Ok(())}
}
fn NMM_readonly_cut(a:&OwnedAccount,p:&Pubkey)->ProgramResult {
 let expected=NMM_readonly_reference(a,p);
 let tag:bool=kani::any();let out=if tag{Ok(())}else{Err(ProgramError::InvalidAccountData)};
 kani::assume(out==expected);out
}
fn NMM_data_cut(a:&OwnedAccount)->Result<&[u8],ProgramError> {
 // Branch domain: existing snapshot's data is a deferred error. No returned
 // borrowed guard or payload is fabricated; all returned errors are retained.
 assert!(a.bytes.is_err(),"deferred-data branch domain");
 match &a.bytes {Err(e)=>Err(e.clone()),Ok(_)=>unreachable!()}
}
fn NMM_key_cut(a:&OwnedAccount)->&Pubkey {&a.key}
fn NMM_pda(_seeds:&[&[u8]],_program:&Pubkey)->Result<Pubkey,solana_program::pubkey::PubkeyError> {
 assert!(false,"PDA must be unreachable on deferred registry-data branch");
 Err(solana_program::pubkey::PubkeyError::InvalidSeeds)
}
fn NMM_account<const N:usize>(err:ProgramError)->OwnedAccount {
 let original:[u8;N]=kani::any();let bytes=Box::new(original).into_vec();
 // A deferred-error snapshot contains no byte value. This allocation checks
 // constructor handling only and is NOT arbitrary-content success coverage.
 drop(bytes);
 OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(N),bytes:Err(err)}
}
'''
ANN='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(super::super::pool_program_id,NMM_pool_cut)]
#[kani::stub(super::super::registry_program_id,NMM_registry_id_cut)]
#[kani::stub(super::require_readonly_account,NMM_readonly_cut)]
#[kani::stub(super::OwnedAccount::data,NMM_data_cut)]
#[kani::stub(super::OwnedAccount::key,NMM_key_cut)]
#[kani::stub(aspis_statement::pool_v1::validate_verifier_policy_v1,NMM_policy_cut)]
#[kani::stub(solana_program::pubkey::Pubkey::create_program_address,NMM_pda)]
'''
def attempt(a,version,mode):
 version=int(version);sizeR,sizeE=(128,192) if version==1 else (256,320)
 ref=(E/'NMM_FROZEN_234.rs').read_text().replace('fn authenticate_invariant_release_registry(', 'fn NMM_registry_reference(',1).replace('validate_verifier_policy_v1(', 'NMM_policy_reference(').replace('require_readonly_account(', 'NMM_readonly_reference(').replace('pool_program_id(', 'NMM_pool_program_id_reference(').replace('registry_program_id(', 'NMM_registry_program_id_reference(')
 text=common()+HELP+ref+ANN+'''fn stage(){
 let master=any_master();let master_account=NMM_account::<1>(ProgramError::InvalidAccountData);
 let registry=NMM_account::<RS>(ProgramError::AccountBorrowFailed);
 let entry=NMM_account::<ES>(ProgramError::InvalidAccountData);
 let verifier=Pubkey::new_from_array(kani::any());let pool=Pubkey::new_from_array(kani::any());
 let slot:u64=kani::any();
 kani::assume((master.verifier_policy.flags&POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT!=0)==V2);
 let native=authenticate_invariant_release_registry(&verifier,&pool,&master_account,&master,&registry,&entry,slot);
 let reference=NMM_registry_reference(&verifier,&pool,&master_account,&master,&registry,&entry,slot);
 assert!(native==reference,"complete actual234 deferred-registry Result branch");
}
'''.replace('RS',str(sizeR)).replace('ES',str(sizeE)).replace('V2','true' if version==2 else 'false')
 if mode=='spec':text=text.replace('Err(e)=>Err(e.clone())','Err(_)=>Err(ProgramError::InvalidArgument)')
 if mode=='argument':text=text.replace('&master,&registry,&entry,slot);','&master,&entry,&registry,slot);',1)
 if mode=='footprint':text=text.replace('kani::assume(out==expected);out','let _=expected;out')
 if mode=='copy':text=text.replace('assert!(native==reference,','let src:[u8;32]=kani::any();let mut dst=[0u8;32];dst.copy_from_slice(&src);assert!(dst!=src,')
 module='NMM_registry'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+module+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(row='TX2:234',version=version,mode=mode,branch='deferred registry data error',actual_parent=True,original_extents=[sizeR,sizeE],assumptions='Both owned byte Results are Err; registry AccountBorrowFailed, entry InvalidAccountData; all descriptor/master fields unrestricted; selected version flag',limits='This is only an error-path branch; no complete234 certificate, no PDA execution or value assumption; constructor provenance not inherited as credit'),indent=2)+'\n')
 return submit(a,'r1_pool_adapter::owned::'+module+'::stage',P,module,text,mode)
if __name__=='__main__':
 import sys
 rc=attempt(*sys.argv[1:]);sys.exit(rc['exit_status'])
