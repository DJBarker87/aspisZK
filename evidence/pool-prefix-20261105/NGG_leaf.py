"""Actual frozen leaf helpers, local records; matched corruptions never earn credit."""
from pathlib import Path
import subprocess,difflib,json,sys,hashlib
E=Path(__file__).resolve().parent;kind,mode=sys.argv[1:3];assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
wide=kind=='count18'
if wide:kind='count'
parent='pair_forest' if kind in ['hints','count'] else 'processor' if kind in ['payer','token'] else 'pair_forest_dispatch'
s='use super::*;\n'
attrs='''#[kani::proof]
#[kani::unwind(325)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
'''
body=''
if kind=='hints':
 body='''let bytes:[u8;324]=kani::any();let len:usize=kani::any();kani::assume(len<=324);
 let result=split_pair_forest_terminal_bump_hints_v1(&bytes[..len]);
 if len<4{assert!(matches!(result,Err(ProgramError::InvalidInstructionData)));}
 else{let (body,h)=result.unwrap();assert!(body.len()==len-4);if len>4{let j:usize=kani::any();kani::assume(j<len-4);assert!(body[j]==bytes[j]);}
 let mut observed=h.encode();CORRUPT assert!(observed==[bytes[len-4],bytes[len-3],bytes[len-2],bytes[len-1]]);}
'''
else:
 body='''let keys:[[u8;32];4]=kani::any();let owners:[[u8;32];3]=kani::any();
 let k0=Pubkey::new_from_array(keys[0]);let k1=Pubkey::new_from_array(keys[1]);let k2=Pubkey::new_from_array(keys[2]);let selected=Pubkey::new_from_array(keys[3]);
 let o0=Pubkey::new_from_array(owners[0]);let o1=Pubkey::new_from_array(owners[1]);let o2=Pubkey::new_from_array(owners[2]);
 let mut l0:u64=kani::any();let mut l1:u64=kani::any();let mut l2:u64=kani::any();let mut d0:[u8;1]=kani::any();let mut d1:[u8;1]=kani::any();let mut d2:[u8;1]=kani::any();
 let f:[bool;9]=kani::any();let epochs:[u64;3]=kani::any();
 let a0=AccountInfo::new(&k0,f[0],f[1],&mut l0,&mut d0,&o0,f[2],epochs[0]);
 let a1=AccountInfo::new(&k1,f[3],f[4],&mut l1,&mut d1,&o1,f[5],epochs[1]);
 let a2=AccountInfo::new(&k2,f[6],f[7],&mut l2,&mut d2,&o2,f[8],epochs[2]);
'''
 if kind=='loader':body+='let mut actual=supported_loader(&o0);let expected=o0==bpf_loader::id()||o0==bpf_loader_upgradeable::id()||o0==loader_v4::id();CORRUPT assert!(actual==expected);'
 elif kind=='verifier':body+='''let mut actual=require_verifier_program(&a0,&selected);let expected=if k0!=selected||!f[2]||f[0]||f[1]||!(o0==bpf_loader::id()||o0==bpf_loader_upgradeable::id()||o0==loader_v4::id()){Err(PoolV1ProgramError::InvalidVerifierProgramAccount.into())}else{Ok(())};CORRUPT assert!(actual==expected);'''
 elif kind=='transport':body+='''let present:bool=kani::any();let cp=if present{Some(&a2)}else{None};let mut actual=proof_transport_verifier(&a0,&a1,cp);let expected=if !present{Err(ProgramError::NotEnoughAccountKeys)}else if k1==k0||f[5]||f[3]||f[4]||o2!=k0||f[8]||f[6]||f[7]||k2==k1||k2==k0{Err(PoolV1ProgramError::InvalidVerifierProofAccount.into())}else{Ok(k0)};CORRUPT assert!(actual==expected);'''
 elif kind=='count':body+='''let all=[a0,a1,a2];let n:usize=kani::any();kani::assume(n<=3);let expected_count:usize=kani::any();let mut actual=require_exact_account_count(&all[..n],expected_count);let expected=if n==expected_count{Ok(())}else if n<expected_count{Err(ProgramError::NotEnoughAccountKeys)}else{Err(ProgramError::InvalidArgument)};CORRUPT assert!(actual==expected);'''
 elif kind=='payer':body+='''let mut actual=require_payer_and_system_program(&a0,&a1);let expected=if !f[0]||!f[1]||f[2]||o0!=system_program::id(){Err(PoolV1ProgramError::InvalidPayer.into())}else if k1!=system_program::id()||o1!=native_loader::id()||!f[5]||f[3]||f[4]{Err(PoolV1ProgramError::InvalidSystemProgram.into())}else{Ok(())};CORRUPT assert!(actual==expected);'''
 elif kind=='token':body+='''let mut actual=require_token_program_account(&a0);let expected=if k0!=LEGACY_SPL_TOKEN_PROGRAM_ID||!f[2]||f[0]||f[1]||!(o0==bpf_loader::id()||o0==bpf_loader_upgradeable::id()||o0==loader_v4::id()){Err(PoolV1ProgramError::InvalidTokenProgram.into())}else{Ok(())};CORRUPT assert!(actual==expected);'''
 else:raise ValueError(kind)
if wide:
 body=body.replace('let all=[a0,a1,a2];',"let all:[AccountInfo<'_>;18]=core::array::from_fn(|_|a0.clone());").replace('kani::assume(n<=3);','kani::assume(n<=18);')
 attrs=attrs.replace('unwind(325)','unwind(1025)')
# Matched control corrupts observed Result/bool, never source names.
corrupt='observed[0]^=1;' if kind=='hints' else 'actual=!actual;' if kind=='loader' else 'actual=if actual.is_ok(){Err(ProgramError::InvalidArgument)}else{Ok(k0)};' if kind=='transport' else 'actual=if actual.is_ok(){Err(ProgramError::InvalidArgument)}else{Ok(())};'
s+=attrs+body.replace('CORRUPT',corrupt if mode=='negative' else '')+'\n}\n'
patch=''
for path in ['programs/aspis-pool/src/'+parent+'.rs','programs/aspis-pool/src/lib.rs']:
 f=read(path);hook=f+'\n#[cfg(kani)]\n#[path="NGG_Leaf.rs"]\nmod NGG_Leaf;\n' if path.endswith(parent+'.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
path='programs/aspis-pool/src/NGG_Leaf.rs';patch+='--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NGG_native.patch').write_text(patch);(E/'NGG_CURRENT.json').write_text(json.dumps(dict(kind='count18' if wide else kind,mode=mode,source=s,parent=parent,modifies=[],domain=('count list length<=18; ' if wide else '')+'all metadata values; data/lamports unused by leaf (source-footprint lifting remains model obligation); hints length <=324; count list length <=3',status='candidate; no composed credit'),indent=1)+'\n')
print(parent+'::NGG_Leaf::association')
