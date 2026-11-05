"""Actual checkpoint caller with explicit local oracle records; exact source erasure."""
from pathlib import Path
import sys,json,re,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E))
from NIO_native_prepare import stage,attrs
from NIO_frozen_identity import frozen
text=frozen()['programs/aspis-pool/src/pair_forest.rs'].decode()
start=text.index('pub(crate) fn process_pair_forest_checkpoint_with_runtime_v1')
end=text.index('\n}\n',start)+2
original=text[start:end]
function=original.replace('process_pair_forest_checkpoint_with_runtime_v1','NIO_checkpoint',1)
function=function.replace('    runtime: &mut R,\n','    runtime: &mut R,\n    nio_log: &mut NIO_Log,\n',1)
wraps=['decode_pair_forest_checkpoint_instruction_v1','require_exact_account_count','require_unique_accounts','require_payer_and_system_program','plan_pair_forest_checkpoint_accounts_v1','plan_fresh_program_pda','require_program_owned_zeroed']
for i,name in enumerate(wraps):function=function.replace(name+'(',f'NIO_call{i}(nio_log, ')
erased=function.replace('NIO_checkpoint','process_pair_forest_checkpoint_with_runtime_v1',1).replace('    nio_log: &mut NIO_Log,\n','',1)
for i,name in enumerate(wraps):erased=erased.replace(f'NIO_call{i}(nio_log, ',name+'(')
assert erased==original,'STOP source erasure mismatch'
(E/'NIO_CHECKPOINT_ERASURE.json').write_text(json.dumps(dict(original_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_sha256=hashlib.sha256(function.encode()).hexdigest(),erasure_equal=True,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',original=original,instrumented=function,wraps=wraps,branch='ProgramOwnedZeroed: creation arm unclaimed'),indent=2)+'\n')
wrappers=r'''
use super::*;
struct NIO_Log {
    next: u8, fail: u8, error: u64,
    plan: Option<PlannedPairForestCheckpointAccountsV1>,
    seen_master: bool, seen_checkpoint: bool, seen_lanes: usize,
}
impl NIO_Log {
 fn step(&mut self, tag:u8)->ProgramResult {
   assert!(self.next==tag);self.next+=1;
   if self.fail==tag { Err(ProgramError::from(self.error)) } else {Ok(())}
 }
}
fn NIO_call0(l:&mut NIO_Log,_data:&[u8])->ProgramResult {l.step(0)}
fn NIO_call1(l:&mut NIO_Log,a:&[AccountInfo<'_>],n:usize)->ProgramResult {
 assert!(a.len()==n);l.step(1)
}
fn NIO_call2(l:&mut NIO_Log,_a:&[AccountInfo<'_>])->ProgramResult {l.step(2)}
fn NIO_call3(l:&mut NIO_Log,p:&AccountInfo<'_>,s:&AccountInfo<'_>)->ProgramResult {
 assert!(p.rent_epoch==10);assert!(s.rent_epoch==11);l.step(3)
}
fn NIO_call4(l:&mut NIO_Log,_pid:&Pubkey,m:&AccountInfo<'_>,lanes:&[AccountInfo<'_>],c:&AccountInfo<'_>)->Result<PlannedPairForestCheckpointAccountsV1,ProgramError>{
 l.seen_master=m.rent_epoch==0;l.seen_checkpoint=c.rent_epoch==9;l.seen_lanes=lanes.len();
 assert!(l.seen_master && l.seen_checkpoint && l.seen_lanes==8);
 l.step(4)?;Ok(l.plan.take().unwrap())
}
fn NIO_call5(l:&mut NIO_Log,c:&AccountInfo<'_>,_pid:&Pubkey,_key:&Pubkey,n:usize)->Result<FreshPdaPreparationV1,ProgramError>{
 assert!(c.rent_epoch==9 && n==POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES);
 l.step(5)?;Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
}
fn NIO_call6(l:&mut NIO_Log,c:&AccountInfo<'_>,_pid:&Pubkey,n:usize,_rent:&Rent)->ProgramResult{
 assert!(c.rent_epoch==9 && n==POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES);l.step(6)
}
struct NIO_Runtime;
impl PoolCpiRuntimeV1 for NIO_Runtime {
 fn invoke<'i>(&mut self,_i:&solana_program::instruction::Instruction,_a:&[AccountInfo<'i>])->ProgramResult {assert!(false);Ok(())}
 fn invoke_signed<'i>(&mut self,_i:&solana_program::instruction::Instruction,_a:&[AccountInfo<'i>],_s:&[&[&[u8]]])->ProgramResult {assert!(false);Ok(())}
}
'''
mode=int(sys.argv[1]);negative=sys.argv[2]=='negative'
setup=''
for i in range(12):
 n=384 if i==0 else 192 if i==9 else 1
 setup+=f'let k{i}=Pubkey::new_from_array(kani::any());let mut balance{i}:u64=kani::any();let mut bytes{i}:[u8;{n}]=kani::any();let a{i}=AccountInfo::new(&k{i},false,true,&mut balance{i},&mut bytes{i},&k{i},false,{i});\n'
setup+='let accounts=['+','.join('a'+str(i) for i in range(12))+'];\n'
setup+='let jm:usize=kani::any();kani::assume(jm<384);let jc:usize=kani::any();kani::assume(jc<192);\n'
setup+='let oldm=accounts[0].try_borrow_data().unwrap()[jm];let oldc=accounts[9].try_borrow_data().unwrap()[jc];\n'
setup+='let plan=PlannedPairForestCheckpointAccountsV1{master:Pubkey::new_from_array(kani::any()),checkpoint:Pubkey::new_from_array(kani::any()),lane_sequences:kani::any(),next_master_image:kani::any(),checkpoint_image:kani::any()};\n'
setup+='let wantm=plan.next_master_image[jm];let wantc=plan.checkpoint_image[jc];let fail:u8=kani::any();let error:u64=kani::any();let mut log=NIO_Log{next:0,fail,error,plan:Some(plan),seen_master:false,seen_checkpoint:false,seen_lanes:0};\n'
if mode==1:setup+='let ambient=accounts[9].try_borrow_data().unwrap();\n'
if mode==2:setup+='let ambient=accounts[0].try_borrow_data().unwrap();\n'
setup+='let result=NIO_checkpoint(&k0,&accounts,&[],&Rent::default(),&mut NIO_Runtime,&mut log);\n'
setup+='if fail<7 {assert!(result==Err(ProgramError::from(error)));assert!(log.next==fail+1);}else{assert!(log.next==7);'
setup+=('assert!(result==Err(ProgramError::AccountBorrowFailed));' if mode else 'assert!(result==Ok(()));')+'}\n'
setup+=('if fail>=7 {assert!(accounts[0].try_borrow_data().unwrap()[jm]==wantm);assert!(accounts[9].try_borrow_data().unwrap()[jc]==wantc);}else{' if mode==0 else '{')
setup+='assert!(accounts[0].try_borrow_data().unwrap()[jm]==oldm);assert!(accounts[9].try_borrow_data().unwrap()[jc]==oldc);}\n'
if mode:setup+='drop(ambient);\n'
if negative:setup+='let _unreleased=accounts[0].try_borrow_mut_data().unwrap();\n'
setup+='assert!(accounts[0].try_borrow_mut_data().is_ok());assert!(accounts[9].try_borrow_mut_data().is_ok());\n'
source=wrappers+'\n'+function+'\n'+attrs()+'\n#[kani::proof]\nfn certificate(){'+setup+'}\n'
stage('programs/aspis-pool/src/pair_forest.rs',source,'source-erased checkpoint caller, local-record zeroed branch',sys.argv[2],f'Full arbitrary master/checkpoint byte arrays and scalar balances; arbitrary explicit-constructor callee errors and plan image; incoming shared counter case {mode}; existing-zeroed preparation branch.','Creation preparation branch, arbitrary ambient counter/alias relation, exact callee laws and every logged argument domain remain OPEN; this source-erased native branch is not a composed Pool row.',dict(expected_verdict='FAIL' if negative else 'PASS',member='process_pair_forest_checkpoint_with_runtime_v1',erasure_file='NIO_CHECKPOINT_ERASURE.json',modifies=['master.data','checkpoint.data','local ghost log']))
print('NIO checkpoint branch prepared; exact source erasure verified')
