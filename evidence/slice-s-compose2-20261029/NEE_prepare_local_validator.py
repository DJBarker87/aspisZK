"""Rule-16 oracle threading, with reversible exact frozen-body projection."""
from pathlib import Path
import difflib,json,hashlib,subprocess,sys
full=len(sys.argv)>1 and sys.argv[1]=='full'
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
name='validate_pool_v1_pair_forest_terminal_statement_v1'
a=frozen.index('pub fn '+name+'(');z=frozen.index('\n}\n',a)+3
body=frozen[a:z]
threaded=body.replace('    statement: &PoolV1PairForestTerminalStatementV1,','    statement: &PoolV1PairForestTerminalStatementV1,\n    frame: &mut NEE_oracle::Frame,')
changes={
 'encode_pool_v1_private_transfer_public_v1(public)':'NEE_oracle::pay_t(public,frame)',
 'encode_pool_v1_withdrawal_public_v1(public)':'NEE_oracle::pay_w(public,frame)',
 'pool_v1_pair_forest_output_lane_v1(&nullifier)':'NEE_oracle::lane(&nullifier,frame)',
 'encode_pool_v1_pair_late_public_statement_v1(&common.lane_transition, &mut late_bytes)':'NEE_oracle::late(&common.lane_transition, &mut late_bytes,frame)'}
for before,after in changes.items():assert threaded.count(before)==1;threaded=threaded.replace(before,after)
project=threaded.replace('    frame: &mut NEE_oracle::Frame,\n','')
for before,after in changes.items():project=project.replace(after,before)
assert project==body
changed=frozen[:a]+'#[cfg(not(kani))]\n'+body+'#[cfg(kani)]\n'+threaded+frozen[z:]
# Other callers are not reached by these harnesses; retain their native source
# verbatim under not(kani), with a type-correct local oracle counterpart.
for arg in ['statement','&statement']:
 old='    '+name+'('+arg+')?;'
 new='    #[cfg(not(kani))]\n'+old+'\n    #[cfg(kani)]\n    '+name+'('+arg+', &mut NEE_oracle::Frame::new('+arg+'))?;'
 changed=changed.replace(old,new)
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
base,hook=oracle_parts()
# The explicit G is copied from the historical oracle reference, unchanged.
old=(E/'NEE_K005-NEE_oracle.patch').read_text().split('--- a/',1)[0]
src='\n'.join(l[1:] for l in old.splitlines()[3:] if l.startswith('+'))+'\n'
ref=src[src.index('fn validator_ref('):src.index('fn oracle_domain(')]
module=base+'''
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct Trace {len:usize,log:[u8;3]}
impl Trace {fn push(&mut self,t:u8){assert!(self.len<3);self.log[self.len]=t;self.len+=1;}}
pub(super) struct Frame<'a> {
 root:&'a PoolV1PairForestTerminalStatementV1,
 payment:Result<[u8;216],PoolV1PaymentStatementFormatError>,
 lane:Result<u8,PoolV1PairForestAccountErrorV1>,
 late:Result<(),PoolV1PairLatePublicStatementErrorV1>,
 trace:Trace,
}
impl<'a> Frame<'a>{pub(super) fn new(root:&'a PoolV1PairForestTerminalStatementV1)->Self {
 Self{root,payment:if kani::any(){Ok(kani::any())}else{Err(NEE_any_PoolV1PaymentStatementFormatError())},
 lane:if kani::any(){Ok(kani::any())}else{Err(NEE_any_PoolV1PairForestAccountErrorV1())},
 late:if kani::any(){Ok(())}else{Err(NEE_any_PoolV1PairLatePublicStatementErrorV1())},
 trace:Trace{len:0,log:[0;3]}}
}}
pub(super) fn pay_t(p:&PoolV1PrivateTransferPublicV1,f:&mut Frame)->Result<[u8;216],PoolV1PaymentStatementFormatError>{
 let expected=match f.root{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>public,_=>panic!("wrong transfer variant")};
 assert!(core::ptr::eq(p,expected));f.trace.push(1);f.payment
}
pub(super) fn pay_w(p:&PoolV1WithdrawalPublicV1,f:&mut Frame)->Result<[u8;216],PoolV1PaymentStatementFormatError>{
 let expected=match f.root{PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>public,_=>panic!("wrong withdrawal variant")};
 assert!(core::ptr::eq(p,expected));f.trace.push(2);f.payment
}
pub(super) fn lane(d:&Digest,f:&mut Frame)->Result<u8,PoolV1PairForestAccountErrorV1>{
 let expected=match f.root{PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>&public.nullifier,PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>&public.nullifier};
 let j:usize=kani::any();kani::assume(j<8);assert!(d[j].0==expected[j].0);f.trace.push(3);f.lane
}
pub(super) fn late(s:&PoolV1PairLatePublicStatementV1,out:&mut[u8],f:&mut Frame)->Result<(),PoolV1PairLatePublicStatementErrorV1>{
 assert!(core::ptr::eq(s,&f.root.common().lane_transition));assert!(out.len()==1520);
 let j=0usize;assert!(out[j]==0);out[j]=kani::any();f.trace.push(4);f.late
}
'''+ref+'''
fn oracle_domain(negative:bool){let s=NEE_statement();let mut f=Frame::new(&s);
 let actual=validate_pool_v1_pair_forest_terminal_statement_v1(&s,&mut f);
 let mut expected_log=Trace{len:0,log:[0;3]};
 let expected=validator_ref(&s,f.payment,f.lane,f.late,&mut expected_log);
 assert!((actual==expected&&f.trace==expected_log)!=negative,"NEE framed oracle Result/order");
 kani::cover!(actual.is_ok(),"NEE validator success");kani::cover!(f.trace.len==3,"NEE all child calls");
}
'''
if full:
 module=module.replace('let j=0usize;assert!(out[j]==0);out[j]=kani::any();', 'let j:usize=kani::any();kani::assume(j<1520);assert!(out[j]==0);out.copy_from_slice(&kani::any::<[u8;1520]>());')
kmx='\n'.join(l[1:] for l in (E/'NEE_K005-NEE_oracle.patch').read_text().splitlines() if l.startswith('+#[kani::stub(') and ('KMX_' in l))
# Historical source has a positive and negative copy of the same stub list.
kmx='\n'.join(dict.fromkeys(kmx.splitlines()))+'\n'
for suffix,negative in [('positive','false'),('negative','true')]:
 module+='#[kani::proof]\n'+kmx+'fn oracle_domain_'+suffix+'(){oracle_domain('+negative+');}\n'
assert 'static mut' not in module
(E/'NEE_native_contracts.patch').write_text(patch)
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(module.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in module.splitlines())+hook)
(E/'NEE_LOCAL_VALIDATOR_PROJECTION.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source=path,body_sha256=hashlib.sha256(body.encode()).hexdigest(),exact_body_projection=project==body,threaded_calls=changes,property_unchanged_from='NEE_K004',harness_names_unchanged=True,local_records_only=True,late_modifies='unconstrained full 1520-byte mutation, arbitrary-index initial-zero check' if full else 'one fixed byte; full unconstrained late mutation remains OPEN',scope='native control with explicit ghost parameter and oracle call substitution; not an unconditional native root theorem'),indent=1)+'\n')
