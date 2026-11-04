from pathlib import Path
import json,sys,subprocess,difflib,re
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','byte-negative','program-negative']
read=lambda p:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
base=json.loads((E.parent/'pool-retdata-20261104/NFO_K056-shape.json').read_text())['source']
accounts=base[base.index(' let selected='):base.index(' let raw:')]
accounts=accounts.replace('let returned=Pubkey::new_from_array(kani::any());kani::assume(returned!=selected);','')
accounts=accounts.replace('let info1=AccountInfo::new(', 'let proof_owner=Pubkey::new_from_array(kani::any());let info1=AccountInfo::new(').replace('&mut data1,&owner,','&mut data1,&proof_owner,')
for i in [6,7]:
 accounts=accounts.replace(f'let info{i}=AccountInfo::new(',f'let registry_owner{i}=Pubkey::new_from_array(kani::any());let info{i}=AccountInfo::new(').replace(f'&mut data{i},&owner,',f'&mut data{i},&registry_owner{i},')
payment=read('crates/aspis-statement/src/pool_v1/payment_relation.rs');helpers='fn digest()->aspis_statement::Digest{core::array::from_fn(|_|aspis_core::field::M31(kani::any()))}\n'
for name in ['PoolV1PrivateTransferPublicV1','PoolV1WithdrawalPublicV1']:
 block=payment.split('pub struct '+name+' {',1)[1].split('\n}',1)[0]
 fields=re.findall(r'pub (\w+):\s*([^\n]+),',block)
 helpers+='fn any_'+name+'()->'+name+'{'+name+'{'+','.join(k+':'+('digest()' if t=='Digest' else 'aspis_core::field::M31(kani::any())' if t=='M31' else 'kani::any()') for k,t in fields)+'}}\n'
policy='VerifierPolicyV1{flags:kani::any(),registry_program:kani::any(),registry_authority:kani::any(),policy_binding:kani::any()}'
registry='''use super::*;
pub(crate) fn authenticate(_: &Pubkey,_:&VerifierPolicyV1,_:&[AccountInfo<'_>],_:VerifierSelectionV1,_:u64)->Result<AuthenticatedVerifierSelectionV1,ProgramError>{
 if kani::any(){Err(ProgramError::from(kani::any::<u64>()))}else{Ok(AuthenticatedVerifierSelectionV1{
 policy:POLICY,pool:kani::any(),verifier_program:kani::any(),profile_binding:kani::any(),release_binding:kani::any(),statement_version:kani::any(),registry_generation:kani::any(),expected_verifier_loader:kani::any(),authenticated_at_slot:kani::any()})}
}
'''.replace('POLICY',policy)
s='use super::*;\nuse aspis_statement::pool_v1::*;\n'+helpers+'''#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(crate::registry::authenticate_verifier_selection_v1,crate::registry::NFV_Oracle::authenticate)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
fn association(){
'''+accounts+'''
 let public=if kani::any(){PoolV1PairForestTerminalPaymentV1::PrivateTransfer(any_PoolV1PrivateTransferPublicV1())}else{PoolV1PairForestTerminalPaymentV1::Withdrawal(any_PoolV1WithdrawalPublicV1())};
 let request=PoolV1PairForestTerminalRequestV1{pool_program:owner.to_bytes(),verifier_profile:kani::any(),verifier_release:kani::any(),public};
 let raw:[u8;320]=kani::any();let bytes:Box<[u8]>=Box::new(raw);let pointer=bytes.as_ptr();let j:usize=kani::any();kani::assume(j<320);let byte=bytes[j];
 let policy=POLICY;
 let actual=plan_pair_forest_terminal_dispatch_with_bytes_v1(&owner,&info3,&info4,&info5,&policy,&[info6,info7],&info0,&info1,Some(&info2),&request,kani::any(),bytes.into_vec());
 if let Ok(plan)=actual{
  CHECK_PROGRAM
  assert!(plan.request_bytes.len()==320&&plan.request_bytes.as_ptr()==pointer);
  CHECK_BYTE
 }
}
'''.replace('POLICY',policy)
s=s.replace('CHECK_PROGRAM','assert!(plan.selected_verifier!=selected);' if mode=='program-negative' else 'assert!(plan.selected_verifier==selected);')
s=s.replace('CHECK_BYTE','assert!(plan.request_bytes[j]==(byte^1));' if mode=='byte-negative' else 'assert!(plan.request_bytes[j]==byte);')
patch=''
for p,hook in [('programs/aspis-pool/src/pair_forest_dispatch.rs','\n#[cfg(kani)]\n#[path="NFV_Plan.rs"]\nmod NFV_Plan;\n'),('programs/aspis-pool/src/registry.rs','\n#[cfg(kani)]\n#[path="NFV_Oracle.rs"]\npub(crate) mod NFV_Oracle;\n'),('programs/aspis-pool/src/lib.rs','\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n')]:
 f=read(p);changed=('#![cfg_attr(kani, feature(allocator_api))]\n' if p.endswith('/lib.rs') else '')+f+hook
 patch+=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
for p,text in [('programs/aspis-pool/src/NFV_Plan.rs',s),('programs/aspis-pool/src/NFV_Oracle.rs',registry)]:
 patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in text.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(mode='plan-'+mode,source=s,registry_oracle=registry,classification='ACTUAL frozen with-bytes planner, accepted-return request ownership and selected-program forwarding only; no outer process/admission or request encoding credit',domain='accepted metadata/key facts; independent proof and registry owners; EMPTY account-data buffers remain an explicit probe restriction, not the production child PacketDomain; raw public fields arbitrary'),indent=1)+'\n')
