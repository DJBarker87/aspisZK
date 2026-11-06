from pathlib import Path
import difflib
E=Path(__file__).resolve().parent;p=E/'NLQ_NATIVE.patch';s=p.read_text()
a=s.index('--- /dev/null\n+++ b/programs/r1-cost-probe/src/NLQ_native.rs\n');b=s.index('--- /dev/null\n+++ b/programs/r1-cost-probe/src/NLQ_adapter.rs\n',a)
raw=''.join(l[1:] for l in s[a:b].splitlines(True) if l.startswith('+') and not l.startswith('+++'))
raw+='''
fn error_reply(_:verifier::Error)->ProgramError {ProgramError::InvalidInstructionData}
fn check_first(bad:bool){
 use aspis_statement::pool_v1::{PoolV1PrivateTransferPublicV1,PoolV1PairLatePublicStatementV1,PoolV1PairLiveSnapshotV1,PoolV1PairVerifiedAfterstateV1};
 use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
 use aspis_core::field::M31;
 let zero=[M31(0);8];
 let transfer=PoolV1PrivateTransferPublicV1{pool:[0;32],deployment_domain:[0;32],anchor_sequence:0,anchor_root:zero,nullifier:zero,asset_id:M31(0),recipient_commitment:zero,change_commitment:zero};
 let late=PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:[0;32],deployment_domain:[0;32],sequence:0,next_pair_index:0,current_root:zero,frontier:[zero;20]},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:0,next_root:zero,next_frontier:[zero;20]}};
 let public_bytes:[u8;2]=kani::any();let proof:[u8;2]=kani::any();
 let p0=public_bytes[0];let p1=public_bytes[1];let r0=proof[0];let r1=proof[1];
 let result=first_decoded(Public::Transfer(&transfer,&late),&public_bytes,&proof,11);
 if bad {assert_eq!(result,Err(ProgramError::InvalidAccountData));}
 else {assert_eq!(result,Err(ProgramError::InvalidInstructionData));}
 assert_eq!(public_bytes[0],p0);assert_eq!(public_bytes[1],p1);assert_eq!(proof[0],r0);assert_eq!(proof[1],r1);
}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(crate::error,error_reply)]
fn first_wrong_split(){check_first(false)}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(crate::error,error_reply)]
fn first_wrong_split_control(){check_first(true)}
'''
p.write_text(s[:a]+''.join(difflib.unified_diff([],raw.splitlines(True),fromfile='/dev/null',tofile='b/programs/r1-cost-probe/src/NLQ_native.rs'))+s[b:])
print('extended patch with actual first_decoded wrong-split returning-error window')
