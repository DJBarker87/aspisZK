use super::*;
fn late()->super::super::pair_tree_profile::PoolV1PairLatePublicStatementV1{
 use crate::pool_v1::{pair_tree_profile::{PoolV1PairLatePublicStatementV1,PoolV1PairLiveSnapshotV1},pair_terminal::PoolV1PairVerifiedAfterstateV1};
 PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:kani::any(),frontier:kani::any()},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:kani::any(),next_frontier:kani::any()}}
}
fn common()->Box<PoolV1PairForestTerminalCommonV1>{Box::new(PoolV1PairForestTerminalCommonV1{master_account:kani::any(),checkpoint_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),checkpoint_sequence:kani::any(),historical_global_anchor:kani::any(),lane_transition:late()})}
#[kani::proof] #[kani::unwind(22)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_transfer_short(){let raw:[u8;8]=kani::any();let len:usize=kani::any();kani::assume(len<=8);let r=super::decode_transfer_statement_boxed_v1(common(),&raw[..len]);let good=matches!(r,Err(PoolV1PairForestTerminalFormatErrorV1::Payment(super::super::payment_relation::PoolV1PaymentStatementFormatError::WrongLength)));assert!(good!=cfg!(NDE_invert));}
#[kani::proof] #[kani::unwind(22)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_withdrawal_short(){let raw:[u8;8]=kani::any();let len:usize=kani::any();kani::assume(len<=8);let r=super::decode_withdrawal_statement_boxed_v1(common(),&raw[..len]);let good=matches!(r,Err(PoolV1PairForestTerminalFormatErrorV1::Payment(super::super::payment_relation::PoolV1PaymentStatementFormatError::WrongLength)));assert!(good!=cfg!(NDE_invert));}
#[kani::proof] #[kani::unwind(22)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_request_short(){let raw:[u8;8]=kani::any();let len:usize=kani::any();kani::assume(len<=8);let r=super::decode_pool_v1_pair_forest_terminal_request_v1(&raw[..len]);let good=matches!(r,Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength));assert!(good!=cfg!(NDE_invert));}
#[path="NDE_terminal_reference.rs"] mod reference;
#[kani::proof] #[kani::unwind(22)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_semantic_view(){
 use crate::pool_v1::payment_relation::{PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1};
 use crate::pool_v1::pair_forest_semantic_terminal::r0::Public;
 let c=*common();
 let statement=if kani::any(){PoolV1PairForestTerminalStatementV1::PrivateTransfer{common:c,public:PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:kani::any(),nullifier:kani::any(),asset_id:kani::any(),recipient_commitment:kani::any(),change_commitment:kani::any()}}}else{PoolV1PairForestTerminalStatementV1::Withdrawal{common:c,public:PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:kani::any(),nullifier:kani::any(),asset_id:kani::any(),amount:kani::any(),destination_token_account:kani::any(),change_commitment:kani::any()}}};
 let expected=reference::terminal_view_ref(match &statement{PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public}=>reference::TerminalView::Transfer(public,&common.lane_transition),PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}=>reference::TerminalView::Withdrawal(public,&common.lane_transition)});
 let got=statement.semantic_public();
 let good=match(got,expected){(Public::Transfer(p,t),reference::TerminalView::Transfer(q,u))=>core::ptr::eq(p,q)&&core::ptr::eq(t,u),(Public::Withdrawal(p,t),reference::TerminalView::Withdrawal(q,u))=>core::ptr::eq(p,q)&&core::ptr::eq(t,u),_=>false};
 assert!(good!=cfg!(NDE_view_invert));
}
