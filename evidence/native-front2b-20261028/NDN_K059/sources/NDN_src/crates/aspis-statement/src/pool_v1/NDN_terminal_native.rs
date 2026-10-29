use super::*;
#[path="NDN_reference.rs"] mod reference;
fn transition_zero()->PoolV1PairLatePublicStatementV1{
 use crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1;
 PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:[0;32],deployment_domain:[0;32],sequence:0,next_pair_index:0,current_root:[M31::ZERO;8],frontier:[[M31::ZERO;8];20]},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:0,next_root:[M31::ZERO;8],next_frontier:[[M31::ZERO;8];20]}}
}
fn common_zero()->PoolV1PairForestTerminalCommonV1{PoolV1PairForestTerminalCommonV1{master_account:[0;32],checkpoint_account:[0;32],selected_lane_account:[0;32],output_lane:0,checkpoint_sequence:0,historical_global_anchor:[M31::ZERO;8],lane_transition:transition_zero()}}
fn payment_error(h:[u8;8],withdraw:bool)->Option<PoolV1PaymentStatementFormatError>{
 let magic=if withdraw{*b"ASWP"}else{*b"ASCP"};let kind=if withdraw{2}else{1};
 if h[0]!=magic[0]||h[1]!=magic[1]||h[2]!=magic[2]||h[3]!=magic[3]{Some(PoolV1PaymentStatementFormatError::WrongMagic)}else if h[4]!=1{Some(PoolV1PaymentStatementFormatError::WrongVersion)}else if h[5]!=kind{Some(PoolV1PaymentStatementFormatError::WrongTransitionKind)}else if h[6]!=1{Some(PoolV1PaymentStatementFormatError::WrongDigestEncoding)}else if h[7]!=0{Some(PoolV1PaymentStatementFormatError::NonZeroReserved)}else{None}
}
#[cfg(NDN_payment_transfer)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn transfer_header_error(){
 let h:[u8;8]=kani::any();let expected=payment_error(h,false);kani::assume(expected.is_some());
 let mut raw=[0u8;POOL_V1_PAYMENT_STATEMENT_BYTES];raw[..8].copy_from_slice(&h);
 let out=super::decode_transfer_statement_boxed_v1(Box::new(common_zero()),&raw);
 let good=match out{Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e))=>Some(e)==expected,_=>false};
 assert!(good!=cfg!(NDN_invert));
}
#[cfg(NDN_payment_withdrawal)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn withdrawal_header_error(){
 let h:[u8;8]=kani::any();let expected=payment_error(h,true);kani::assume(expected.is_some());
 let mut raw=[0u8;POOL_V1_PAYMENT_STATEMENT_BYTES];raw[..8].copy_from_slice(&h);
 let out=super::decode_withdrawal_statement_boxed_v1(Box::new(common_zero()),&raw);
 let good=match out{Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e))=>Some(e)==expected,_=>false};
 assert!(good!=cfg!(NDN_invert));
}
pub(super) static mut REQ_REACHED:bool=false;
pub(super) static mut REQ_INDEX:usize=0;
pub(super) static mut REQ_VALUE:u8=0;
pub(super) static mut REQ_LENGTH:usize=0;
pub(super) static mut REQ_KIND:u8=0;
#[cfg(NDN_request_cut)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn request_header_window(){
 let h:[u8;8]=kani::any();let j:usize=kani::any();let value:u8=kani::any();kani::assume(j<216);
 let mut raw=[0u8;POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES];raw[..8].copy_from_slice(&h);raw[104+j]=value;
 unsafe{REQ_REACHED=false;REQ_INDEX=j;}
 let r=super::decode_pool_v1_pair_forest_terminal_request_v1(&raw);
 let status=match r{Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength) if unsafe{REQ_REACHED}=>0,Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength)=>1,Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)=>2,Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion)=>3,Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind)=>4,Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding)=>5,Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)=>6,_=>255};
 let expected=if cfg!(NDN_old_header_ref){reference::header_gate(h,320)}else{reference::request_gate(h,320)};
 let payload=if status==0{unsafe{REQ_LENGTH==216&&REQ_VALUE==value&&REQ_KIND==h[5]}}else{!unsafe{REQ_REACHED}};
 assert!((status==expected&&payload)!=cfg!(NDN_invert));
}
pub(super) static mut RESULT_HEADER:[u8;8]=[0;8];
#[cfg(NDN_result_header)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn result_header_window(){
 let kind=if kani::any(){PoolV1TransitionKind::PrivateTransfer}else{PoolV1TransitionKind::Withdrawal};let lane:u8=kani::any();let j:usize=kani::any();kani::assume(j<8);
 let result=PoolV1PairForestTerminalResultV1{transition_kind:kind,master_account:[0;32],selected_lane_account:[0;32],output_lane:lane,nullifier:[M31::ZERO;8],verified_afterstate:transition_zero().candidate_afterstate};
 let _=super::encode_pool_v1_pair_forest_terminal_result_v1(&result);
 assert!((unsafe{RESULT_HEADER[j]}==reference::output_header(j,kind as u8,lane))!=cfg!(NDN_invert));
}
fn transfer_zero()->PoolV1PrivateTransferPublicV1{PoolV1PrivateTransferPublicV1{pool:[0;32],deployment_domain:[0;32],anchor_sequence:0,anchor_root:[M31::ZERO;8],nullifier:[M31::ZERO;8],asset_id:M31::ZERO,recipient_commitment:[M31::ZERO;8],change_commitment:[M31::ZERO;8]}}
#[cfg(NDN_result_compare)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn result_rejection_window(){
 let which:usize=kani::any();let value:u8=kani::any();kani::assume(which<4&&value!=0);
 let statement=PoolV1PairForestTerminalStatementV1::PrivateTransfer{common:common_zero(),public:transfer_zero()};
 let mut result=PoolV1PairForestTerminalResultV1{transition_kind:PoolV1TransitionKind::PrivateTransfer,master_account:[0;32],selected_lane_account:[0;32],output_lane:0,nullifier:[M31::ZERO;8],verified_afterstate:transition_zero().candidate_afterstate};
 match which{0=>result.transition_kind=PoolV1TransitionKind::Withdrawal,1=>result.output_lane=value,2=>result.nullifier[0]=M31(u32::from(value)),_=>result.verified_afterstate.next_pair_index=u64::from(value)}
 let r=super::validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement,&result);
 let good=matches!(r,Err(PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch));assert!(good!=cfg!(NDN_invert));
}
pub(super) static mut COMPARE_J:usize=0;
pub(super) static mut COMPARE_MASTER:(u8,u8)=(0,0);
pub(super) static mut COMPARE_LANE:(u8,u8)=(0,0);
#[cfg(NDN_result_field)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn result_field_window(){
 let j:usize=kani::any();let a:u8=kani::any();let b:u8=kani::any();let c:u8=kani::any();let d:u8=kani::any();kani::assume(j<32);
 let mut common=common_zero();common.master_account[j]=a;common.selected_lane_account[j]=b;
 let statement=PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:transfer_zero()};
 let mut result=PoolV1PairForestTerminalResultV1{transition_kind:PoolV1TransitionKind::PrivateTransfer,master_account:[0;32],selected_lane_account:[0;32],output_lane:0,nullifier:[M31::ZERO;8],verified_afterstate:transition_zero().candidate_afterstate};result.master_account[j]=c;result.selected_lane_account[j]=d;unsafe{COMPARE_J=j;}
 let _=super::validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement,&result);
 assert!(unsafe{COMPARE_MASTER==(c,a)&&COMPARE_LANE==(d,b)});
}
