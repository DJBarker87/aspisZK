"""Frozen request-encoder caller, full typed child Results, one output window."""
from pathlib import Path
import subprocess,json,sys,re,difflib,hashlib
E=Path(__file__).resolve().parent;window=int(sys.argv[1]);mode=sys.argv[2]
assert 0<=window<5 and mode in ['positive','byte-negative','argument-negative','error-negative','guard-negative']
read=lambda p:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';src=read(p);a=src.index('pub fn encode_pool_v1_pair_forest_terminal_request_v1(');z=src.index('\n}',a)+2;original=src[a:z]
body=original[original.index('{\n')+2:original.rindex('}')]
for k,v in json.loads((E/'NFV_REFERENCE_INPUTS.json').read_text())['offsets'].items():body=body.replace(k,str(v))
body=body.replace('encode_pool_v1_private_transfer_public_v1(&public)','transfer(&public)').replace('encode_pool_v1_withdrawal_public_v1(&public)','withdrawal(&public)')
if mode=='argument-negative':body=body.replace('transfer(&public)','transfer(&{let mut wrong=public;wrong.pool[0]^=1;wrong})').replace('withdrawal(&public)','withdrawal(&{let mut wrong=public;wrong.pool[0]^=1;wrong})')
if mode=='error-negative':body=body.replace('.map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?','.map_err(|_|PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)?')
if mode=='guard-negative':body=body.replace('request.verifier_profile == [0u8; 32]','request.verifier_profile != [0u8; 32]',1)
s='use super::*;\nuse aspis_statement::pool_v1::*;\nuse aspis_core::field::M31;\nfn digest()->aspis_statement::Digest{core::array::from_fn(|_|M31(kani::any()))}\n'
payment=read('crates/aspis-statement/src/pool_v1/payment_relation.rs')
for name in ['PoolV1PrivateTransferPublicV1','PoolV1WithdrawalPublicV1']:
 block=payment.split('pub struct '+name+' {',1)[1].split('\n}',1)[0];fields=re.findall(r'pub (\w+):\s*([^\n]+),',block)
 s+='fn any_'+name+'()->'+name+'{'+name+'{'+','.join(k+':'+('digest()' if t=='Digest' else 'M31(kani::any())' if t=='M31' else 'kani::any()') for k,t in fields)+'}}\n'
base=json.loads((E.parent/'pool-retdata2-20261104/NFR_K034-shape.json').read_text())['source']
a=base.index('fn NFO_any_PoolV1PaymentStatementFormatError(');s+=base[a:base.index('\n',a)]+'\n'
s+='''fn native<T,W>(request:&PoolV1PairForestTerminalRequestV1,transfer:T,withdrawal:W)->Result<[u8;320],PoolV1PairForestTerminalFormatErrorV1>
where T:FnOnce(&PoolV1PrivateTransferPublicV1)->Result<[u8;216],PoolV1PaymentStatementFormatError>,W:FnOnce(&PoolV1WithdrawalPublicV1)->Result<[u8;216],PoolV1PaymentStatementFormatError>{
'''+body+'}\n'
s+='''#[kani::proof]
#[kani::unwind(321)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let public=if kani::any(){PoolV1PairForestTerminalPaymentV1::PrivateTransfer(any_PoolV1PrivateTransferPublicV1())}else{PoolV1PairForestTerminalPaymentV1::Withdrawal(any_PoolV1WithdrawalPublicV1())};
 let request=PoolV1PairForestTerminalRequestV1{verifier_profile:kani::any(),verifier_release:kani::any(),pool_program:kani::any(),public};
 let expected_t=match public{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>Some(p),_=>None};
 let expected_w=match public{PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>Some(p),_=>None};
 let kind=if expected_t.is_some(){1u8}else{2u8};
 let child:Result<[u8;216],PoolV1PaymentStatementFormatError>=if kani::any(){Ok(kani::any())}else{Err(NFO_any_PoolV1PaymentStatementFormatError())};
 let j:usize=kani::any();kani::assume(START<=j&&j<END);
 let zero=request.verifier_profile==[0u8;32]||request.verifier_release==[0u8;32]||request.pool_program==[0u8;32];
 let mut t_calls=0u8;let mut w_calls=0u8;
 let mut actual=native(&request,|arg|{t_calls+=1;assert!(Some(*arg)==expected_t);child},|arg|{w_calls+=1;assert!(Some(*arg)==expected_w);child});
 CORRUPTION
 if zero{assert!(t_calls==0&&w_calls==0&&matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)));}
 else{
  assert!(t_calls==if kind==1{1}else{0});assert!(w_calls==if kind==2{1}else{0});
  match child{
   Err(error)=>assert!(matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e)) if e==error)),
   Ok(payment)=>{let bytes=actual.unwrap();let expected=EXPECTED;assert!(bytes[j]==expected);}
  }
 }
}
'''
bounds=[(0,8),(8,40),(40,72),(72,104),(104,320)];start,end=bounds[window]
expected=['match j{0=>b\'A\',1=>b\'S\',2=>b\'Q\',3=>b\'8\',4=>1,5=>kind,6=>1,_=>0}','request.verifier_profile[j-8]','request.verifier_release[j-40]','request.pool_program[j-72]','payment[j-104]'][window]
s=s.replace('START',str(start)).replace('END',str(end)).replace('EXPECTED',expected).replace('CORRUPTION','if let Ok(ref mut bytes)=actual{bytes[j]^=1;}' if mode=='byte-negative' else '')
patch=''
for path in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 f=read(path);hook=f+'\n#[cfg(kani)]\n#[path="NFV_Request.rs"]\nmod NFV_Request;\n' if path.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
path='programs/aspis-pool/src/NFV_Request.rs';patch+='--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(mode='request-'+mode,window=window,range=[start,end],source=s,frozen_function_sha256=hashlib.sha256(original.encode()).hexdigest(),classification='source-exact frozen request-encoder native call-log cut; two full typed payment-child Results; output one arbitrary window byte; all guard/error/call-order paths retained; no field arithmetic or SHA',domain='all valid typed request/public records; each closed payment-child PacketDomain must still be derived from SAME admitted decoder in outer prefix B'),indent=1)+'\n')
