"""Full frozen request decoder with scalar child reply projection and one field."""
from NFD_native_patch import E,frozen,helpers
from NFD_source_tools import calls
import sys,subprocess,json,difflib
slot=int(sys.argv[1]);mode=sys.argv[2];assert 0<=slot<14 and mode in ['positive','value','argument']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';f=frozen(p);name='decode_pool_v1_pair_forest_terminal_request_v1';a=f.index('pub fn '+name+'(');z=f.index('\n}',a)+2;original=f[a:z]
native=original.replace('pub fn '+name+'(','fn native(').replace('    bytes: &[u8],','    bytes: &[u8],f:&mut Frame,')
for old,new in [('decode_pool_v1_private_transfer_public_v1','transfer'),('decode_pool_v1_withdrawal_public_v1','withdrawal')]:native=calls(native,old,new,'f')
if mode=='argument':native=native.replace('bytes[REQUEST_PAYMENT_OFFSET..]','bytes[REQUEST_PAYMENT_OFFSET+1..]')
fields=['pool[j]','deployment_domain[j]','anchor_sequence','anchor_root[i].0','nullifier[i].0','asset_id.0','change_commitment[i].0']
projections=[]
for k in range(11):
 if k==0:ex='match p{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)=>1,PoolV1PairForestTerminalPaymentV1::Withdrawal(_)=>2}'
 elif k<=7:ex='match p{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p.'+fields[k-1]+' as u64,PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>p.'+fields[k-1]+' as u64}'
 else:
  ty='PrivateTransfer' if k==8 else 'Withdrawal';expr=['recipient_commitment[i].0','amount','destination_token_account[j]'][k-8]
  ex='match p{PoolV1PairForestTerminalPaymentV1::'+ty+'(p)=>p.'+expr+' as u64,_=>0}'
 projections.append(ex)
# Only one projection is present in each native harness.
ps=0 if slot<3 else slot-3
project='fn project(p:&PoolV1PairForestTerminalPaymentV1,i:usize,j:usize)->u64{'+projections[ps]+'}'
body=helpers().replace('aspis_statement::','crate::')+project+'''
struct Frame<'a>{bytes:&'a [u8;320],calls:u8,ok:bool,error:PoolV1PaymentStatementFormatError,observed:u64,i:usize,j:usize}
fn transfer(bytes:&[u8],f:&mut Frame)->Result<PoolV1PrivateTransferPublicV1,PoolV1PaymentStatementFormatError>{assert!(f.calls==0&&bytes.len()==216&&core::ptr::eq(bytes.as_ptr(),f.bytes[104..].as_ptr())&&f.bytes[5]==1);f.calls=1;f.ok=kani::any();if f.ok{let s=NEE_statement();let p=match s{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>public,_=>{kani::assume(false);unreachable!()}};f.observed=project(&PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p),f.i,f.j);Ok(p)}else{Err(f.error)}}
fn withdrawal(bytes:&[u8],f:&mut Frame)->Result<PoolV1WithdrawalPublicV1,PoolV1PaymentStatementFormatError>{assert!(f.calls==0&&bytes.len()==216&&core::ptr::eq(bytes.as_ptr(),f.bytes[104..].as_ptr())&&f.bytes[5]==2);f.calls=1;f.ok=kani::any();if f.ok{let s=NEE_statement();let p=match s{PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>public,_=>{kani::assume(false);unreachable!()}};f.observed=project(&PoolV1PairForestTerminalPaymentV1::Withdrawal(p),f.i,f.j);Ok(p)}else{Err(f.error)}}
'''+native+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn request(){let bytes:[u8;320]=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<8&&j<32);let mut f=Frame{bytes:&bytes,calls:0,ok:false,error:NEE_any_PoolV1PaymentStatementFormatError(),observed:0,i,j};let actual=native(&bytes,&mut f);
let header=if bytes[0]!=65||bytes[1]!=83||bytes[2]!=81||bytes[3]!=56{Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)}else if bytes[4]!=1{Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)}else if bytes[5]!=1&&bytes[5]!=2{Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)}else if bytes[6]!=1{Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)}else if bytes[7]!=0{Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}else{Ok(())};
match header{Err(e)=>{assert!(f.calls==0);assert!(matches!(actual,Err(x) if x==e));},Ok(())=>{assert!(f.calls==1);if !f.ok{assert!(matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::Payment(x)) if x==f.error));}else{let zero=bytes[8..40]==[0u8;32]||bytes[40..72]==[0u8;32]||bytes[72..104]==[0u8;32];if zero{assert!(matches!(actual,Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)));}else{match actual{Ok(r)=>{assert!(@OBSERVED@==@EXPECTED@@BAD@);},_=>assert!(false)}}}}}}
'''
obs=['r.verifier_profile[j] as u64','r.verifier_release[j] as u64','r.pool_program[j] as u64','project(&r.public,i,j)'][min(slot,3)]
exp=['bytes[8+j] as u64','bytes[40+j] as u64','bytes[72+j] as u64','f.observed'][min(slot,3)]
if mode=='value' and slot>=11:
 body=body.replace('let i:usize=kani::any();', 'kani::assume(bytes[5]=='+('1' if slot==11 else '2')+');let i:usize=kani::any();')
body=body.replace('@OBSERVED@',obs).replace('@EXPECTED@',exp).replace('@BAD@','^1' if mode=='value' else '')
h=f+'\n#[cfg(kani)]\n#[path="NFD_request.rs"]\nmod NFD_request;\n'
patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NFD_request.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines());(E/'NFD_native_contracts.patch').write_text(patch)
(E/'NFD_REQUEST_CURRENT.json').write_text(json.dumps(dict(mode=mode,field_slot=slot,frozen_body=original,native=native,source=body,domain='every live320-byte request and arbitrary full payment Result, every typed payment field, byte/limb coordinates; length gate separate',classification='full actual request caller, scalar-only child observation, same payment slice, complete errors/order and one returned field'),indent=1)+'\n')
