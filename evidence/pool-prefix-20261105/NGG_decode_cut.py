"""Source-exact first Pool caller cut; no decoder-domain closure is inferred."""
from pathlib import Path
import json,sys,subprocess,difflib,re,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','argument','reply','error','allocation','account']
accepted=len(sys.argv)>3 and sys.argv[3]=='accepted'
family=sys.argv[2] if len(sys.argv)>2 else 'all'
assert family in ['all','place','accounts','hints','errors','profile','release','program','place324','errors324','reject','kind'] or family.startswith('field:')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
p='programs/aspis-pool/src/pair_forest.rs';src=read(p)
a=src.index('    let (request_bytes, hints) =',src.index('pub(crate) fn process_pair_forest_terminal_with_verifier_v1'));b=src.index('    let master = decode_terminal_master_box_v1',a);body=src[a:b]
body=body.replace('decode_terminal_request_box_v1(request_bytes)','decode(request_bytes)')
if mode=='argument':body=body.replace('decode(request_bytes)','decode(&request_bytes[1..])')
s='use super::*;\nuse aspis_statement::pool_v1::*;\n'
payment=read('crates/aspis-statement/src/pool_v1/payment_relation.rs')
s+='fn digest()->aspis_statement::Digest{core::array::from_fn(|_|aspis_core::field::M31(kani::any()))}\n'
for name in ['PoolV1PrivateTransferPublicV1','PoolV1WithdrawalPublicV1']:
 fields=re.findall(r'pub (\w+):\s*([^\n]+),',payment.split('pub struct '+name+' {',1)[1].split('\n}',1)[0])
 s+='fn any_'+name+'()->'+name+'{'+name+'{'+','.join(k+':'+('digest()' if t=='Digest' else 'aspis_core::field::M31(kani::any())' if t=='M31' else 'kani::any()') for k,t in fields)+'}}\n'
s+='''fn prefix<'a,'b,F>(accounts:&'a [AccountInfo<'b>],instruction_data:&[u8],decode:F)->Result<(Box<PoolV1PairForestTerminalRequestV1>,&'a AccountInfo<'b>,&'a AccountInfo<'b>,&'a AccountInfo<'b>,PoolV1PairForestTerminalBumpHintsV1),ProgramError>
where F:FnOnce(&[u8])->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError>{
'''+body
s+='Ok((request,master_account,checkpoint_account,lane_account,hints))\n}\n'
s+='''#[kani::proof]
#[kani::unwind(325)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let raw:[u8;324]=kani::any();let len:usize=kani::any();kani::assume(len<=324);
 let keys:[[u8;32];3]=kani::any();let k0=Pubkey::new_from_array(keys[0]);let k1=Pubkey::new_from_array(keys[1]);let k2=Pubkey::new_from_array(keys[2]);let owner=Pubkey::new_from_array(kani::any());
 let mut l0:u64=kani::any();let mut l1:u64=kani::any();let mut l2:u64=kani::any();let mut d0:[u8;1]=kani::any();let mut d1:[u8;1]=kani::any();let mut d2:[u8;1]=kani::any();let flags:[bool;9]=kani::any();
 let a0=AccountInfo::new(&k0,flags[0],flags[1],&mut l0,&mut d0,&owner,flags[2],0);
 let a1=AccountInfo::new(&k1,flags[3],flags[4],&mut l1,&mut d1,&owner,flags[5],0);
 let a2=AccountInfo::new(&k2,flags[6],flags[7],&mut l2,&mut d2,&owner,flags[8],0);
 let accounts=[a0,a1,a2];let count:usize=kani::any();kani::assume(count<=3);
 let public=if kani::any(){PoolV1PairForestTerminalPaymentV1::PrivateTransfer(any_PoolV1PrivateTransferPublicV1())}else{PoolV1PairForestTerminalPaymentV1::Withdrawal(any_PoolV1WithdrawalPublicV1())};
 let request=PoolV1PairForestTerminalRequestV1{verifier_profile:kani::any(),verifier_release:kani::any(),pool_program:kani::any(),public};
 let success:bool=kani::any();let error=ProgramError::from(kani::any::<u64>());
 let boxed=Box::new(request);let pointer=boxed.as_ref() as *const PoolV1PairForestTerminalRequestV1;
 let mut calls=0u8;
 let mut result=prefix(&accounts[..count],&raw[..len],|arg|{
  calls+=1;assert!(len>=4&&arg.as_ptr()==raw.as_ptr()&&arg.len()==len-4);
  if success{Ok(boxed)}else{Err(error.clone())}
 });
 CORRUPT
 if len<4{assert!(calls==0&&matches!(result,Err(ProgramError::InvalidInstructionData)));}
 else{assert!(calls==1);if !success{assert!(matches!(result,Err(ref e) if *e==error));}
 else if count<3{assert!(matches!(result,Err(ProgramError::NotEnoughAccountKeys)));}
 else{let (r,m,c,l,h)=result.unwrap();assert!(r.as_ref() as *const _==pointer);assert!(*r==request);
 assert!(core::ptr::eq(m,&accounts[0])&&core::ptr::eq(c,&accounts[1])&&core::ptr::eq(l,&accounts[2]));
 assert!(h.encode()==[raw[len-4],raw[len-3],raw[len-2],raw[len-1]]);}}
}
'''
if accepted:
 s=s.replace('kani::assume(len<=324);','kani::assume(len==324);').replace('kani::assume(count<=3);','kani::assume(count==3);')
 s=s.replace('let success:bool=kani::any();let error=ProgramError::from(kani::any::<u64>());','let success=true;let error=ProgramError::InvalidInstructionData;')
if family.endswith('324'):s=s.replace('kani::assume(len<=324);','kani::assume(len==324);')
if family!='all':
 s=s.replace('assert!(*r==request);','')
 if family not in ['place','place324','profile','release','program']:s=s.replace('assert!(r.as_ref() as *const _==pointer);','')
 if family!='accounts':s=s.replace('assert!(core::ptr::eq(m,&accounts[0])&&core::ptr::eq(c,&accounts[1])&&core::ptr::eq(l,&accounts[2]));','')
 if family!='hints':s=s.replace('assert!(h.encode()==[raw[len-4],raw[len-3],raw[len-2],raw[len-1]]);','')
 if family in ['profile','release','program']:
  field={'profile':'verifier_profile','release':'verifier_release','program':'pool_program'}[family]
  s=s.replace('assert!(r.as_ref() as *const _==pointer);',f'let j:usize=kani::any();kani::assume(j<32);assert!(r.{field}[j]==request.{field}[j]);')
if family=='kind' or family.startswith('field:'):
 field=family.split(':',1)[1] if ':' in family else None
 if field in ['pool','deployment_domain','destination_token_account']:check='let j:usize=kani::any();kani::assume(j<32);assert!(a.FIELD[j]==b.FIELD[j]);'
 elif field in ['anchor_root','nullifier','recipient_commitment','change_commitment']:check='let j:usize=kani::any();kani::assume(j<8);assert!(a.FIELD[j].0==b.FIELD[j].0);'
 elif field=='asset_id':check='assert!(a.asset_id.0==b.asset_id.0);'
 elif field:check='assert!(a.FIELD==b.FIELD);'
 else:check=''
 if field:check=check.replace('FIELD',field)
 arms=[]
 for variant in ['PrivateTransfer','Withdrawal']:
  active=not(field=='recipient_commitment' and variant=='Withdrawal') and not(field in ['amount','destination_token_account'] and variant=='PrivateTransfer')
  arms.append(f'(PoolV1PairForestTerminalPaymentV1::{variant}(a),PoolV1PairForestTerminalPaymentV1::{variant}(b))=>{{'+(check if active else '')+'}')
 observation='match (&r.public,&request.public){'+','.join(arms)+',_=>panic!("request kind changed")};'
 s=s.replace('let (r,m,c,l,h)=result.unwrap();','let (r,m,c,l,h)=result.unwrap();'+observation)
if family=='reject':
 s=s[:s.index('fn association(){')]+"""fn association(){
 let raw:[u8;324]=kani::any();let len:usize=kani::any();kani::assume(len<=324);
 let error=ProgramError::from(kani::any::<u64>());let mut calls=0u8;
 let mut result=prefix(&[],&raw[..len],|arg|{calls+=1;assert!(arg.as_ptr()==raw.as_ptr()&&arg.len()==len-4);Err(error.clone())});
 if NEGATE {result=Err(ProgramError::InvalidSeeds);}
 if len<4{assert!(calls==0&&matches!(result,Err(ProgramError::InvalidInstructionData)));}
 else{assert!(calls==1&&matches!(result,Err(ref e) if *e==error));}
}
""".replace('NEGATE','true' if mode=='error' else 'false')
control={'positive':'','argument':'','reply':'if let Ok((ref mut r,_,_,_,_))=result{r.verifier_profile[0]^=1;}','error':'if let Err(ref mut e)=result{*e=ProgramError::InvalidSeeds;}','allocation':'if let Ok((ref mut r,_,_,_,_))=result{let replacement=Box::new(**r);let _retained=r;/* control rebuilt below */}', 'account':'if let Ok((_,ref mut m,_,_,_))=result{*m=&accounts[1];}'}[mode]
if mode=='reply' and family in ['profile','release','program']:
 field={'profile':'verifier_profile','release':'verifier_release','program':'pool_program'}[family]
 control=f'if let Ok((ref mut r,_,_,_,_))=result{{r.{field}[0]^=1;}}'
if mode=='reply' and family=='hints':control='if let Ok((_,_,_,_,ref mut h))=result{h.current_page^=1;}'
if mode=='reply' and family.startswith('field:'):
 field=family.split(':',1)[1]
 suffix='[0]^=1' if field in ['pool','deployment_domain','destination_token_account'] else '[0].0^=1' if field in ['anchor_root','nullifier','recipient_commitment','change_commitment'] else '.0^=1' if field=='asset_id' else '^=1'
 arms=[]
 for variant in ['PrivateTransfer','Withdrawal']:
  if (field=='recipient_commitment' and variant=='Withdrawal') or (field in ['amount','destination_token_account'] and variant=='PrivateTransfer'):continue
  arms.append(f'PoolV1PairForestTerminalPaymentV1::{variant}(ref mut p)=>{{p.{field}{suffix};}}')
 control='if let Ok((ref mut r,_,_,_,_))=result{match r.public{'+','.join(arms)+',_=>{}}}'
if mode=='reply' and family=='kind':
 control='if let Ok((ref mut r,_,_,_,_))=result{r.public=match r.public{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)=>PoolV1PairForestTerminalPaymentV1::Withdrawal(any_PoolV1WithdrawalPublicV1()),_=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(any_PoolV1PrivateTransferPublicV1())};}'
if mode=='allocation':
 s=s.replace(' CORRUPT',' let retained=result.as_ref().ok().map(|(r,_,_,_,_)|Box::new(**r));\n if let (Ok((r,_,_,_,_)),Some(other))=(&mut result,retained){let original=core::mem::replace(r,other);assert!(!core::ptr::eq(r.as_ref(),original.as_ref()));core::mem::forget(original);}')
else:s=s.replace('CORRUPT',control)
patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);hook=f+'\n#[cfg(kani)]\n#[path="NGG_DecodeCut.rs"]\nmod NGG_DecodeCut;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NGG_DecodeCut.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NGG_native.patch').write_text(patch);(E/'NGG_CURRENT.json').write_text(json.dumps(dict(kind='decode-cut',mode=mode,family=family,accepted_only=accepted,source=s,source_span_sha256=hashlib.sha256(src[a:b].encode()).hexdigest(),adaptation='first process cut; sole decoder call replaced by local closure, exact full typed Result; terminal continuation returns named cut values',domain='len<=324, account count<=3; native production decoder domains and subsequent master/checkpoint/lane admission OPEN',modifies=[]),indent=1)+'\n')
