use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
fn any_error()->Error {let tag:u8=kani::any();kani::assume(tag<=10);let row:u8=kani::any();let actual:u8=kani::any();let n:usize=kani::any();match tag {0=>Error::Allocation,1=>Error::RowOrder{expected:row,actual},2=>Error::InvalidRow,3=>Error::Tag{row},4=>Error::Length{row},5=>Error::NonCanonical{row,value:n},6=>Error::Boundary{round:n},7=>Error::Terminal,8=>Error::EqualCirclePoints,9=>Error::TrailingBytes,_=>Error::Public}}
struct Log{expected_owner:*const alloc::vec::Vec<u8>,calls:usize,window:usize,fail:bool,error:Error,seen:bool,frontier:bool,row:usize,word:usize,value:u32,length:usize,owner:*const alloc::vec::Vec<u8>}
fn NHG_fields(out:&mut alloc::vec::Vec<u8>,s:&[M31],log:&mut Log)->Result<(),Error>{assert_eq!(out as *const _,log.expected_owner);let j=log.calls;log.calls+=1;if j==log.window{log.seen=true;log.frontier=false;log.length=s.len();log.value=s[log.word%s.len()].0;log.owner=out;if log.fail{return Err(log.error)}}Ok(())}
fn NHG_frontier(out:&mut alloc::vec::Vec<u8>,s:&[Digest;20],log:&mut Log)->Result<(),Error>{assert_eq!(out as *const _,log.expected_owner);let j=log.calls;log.calls+=1;if j==log.window{log.seen=true;log.frontier=true;log.length=20;log.value=s[log.row][log.word].0;log.owner=out;if log.fail{return Err(log.error)}}Ok(())}
fn NHG_public_plan(public:Public<'_>,log:&mut Log)->Result<alloc::vec::Vec<u8>,Error>{
            let p = public.semantic();
            let mut out = Vec::new();
            out.push(match p.variant {
                CompiledVariant::PrivateTransfer => 0,
                CompiledVariant::Withdrawal => 1,
            });
            NHG_fields(&mut out, &p.anchor,log)?;
            NHG_fields(&mut out, &p.nullifier,log)?;
            NHG_fields(&mut out, &[p.asset_id],log)?;
            out.push(u8::from(p.recipient.is_some()));
            if let Some(value) = p.recipient {
                NHG_fields(&mut out, &value,log)?;
            }
            NHG_fields(&mut out, &p.change,log)?;
            out.push(u8::from(p.withdrawal_amount.is_some()));
            if let Some(value) = p.withdrawal_amount {
                NHG_fields(&mut out, &[M31(value)],log)?;
            }
            let source = p.transition.live_snapshot;
            let after = p.transition.candidate_afterstate;
            out.extend_from_slice(&source.next_pair_index.to_le_bytes());
            NHG_frontier(&mut out, &source.frontier,log)?;
            NHG_fields(&mut out, &after.next_root,log)?;
            NHG_frontier(&mut out, &after.next_frontier,log)?;
            Ok(out)
}
#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_public_routing(){
 let p=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()};
 let w=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()};
 // Fully arbitrary typed transition: no zero/sparse prestate restriction.
 let t=PoolV1PairLatePublicStatementV1{
  live_snapshot:crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{
   pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:core::array::from_fn(|_|digest())},
  candidate_afterstate:crate::pool_v1::PoolV1PairVerifiedAfterstateV1{
   next_pair_index:kani::any(),next_root:digest(),next_frontier:core::array::from_fn(|_|digest())}};
 let withdrawal:bool=kani::any();let public=if withdrawal{Public::Withdrawal(&w,&t)}else{Public::Transfer(&p,&t)};

 let window:usize=kani::any();kani::assume(window<8);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let fail:bool=kani::any();let error=any_error();
 let mut log=Log{expected_owner:core::ptr::null(),calls:0,window,fail,error,seen:false,frontier:false,row,word,value:0,length:0,owner:core::ptr::null()};
 let got=NHG_public_plan(public,&mut log);assert!(log.seen);assert_eq!(log.calls,if fail{window+1}else{8});
 let expected=match window{0=>if withdrawal{w.anchor_root[word].0}else{p.anchor_root[word].0},1=>if withdrawal{w.nullifier[word].0}else{p.nullifier[word].0},2=>if withdrawal{w.asset_id.0}else{p.asset_id.0},3=>if withdrawal{w.change_commitment[word].0}else{p.recipient_commitment[word].0},4=>if withdrawal{w.amount}else{p.change_commitment[word].0},5=>t.live_snapshot.frontier[row][word].0,6=>t.candidate_afterstate.next_root[word].0,_=>t.candidate_afterstate.next_frontier[row][word].0};
 assert_eq!(log.value,expected^if cfg!(NHG_invert){1}else{0});assert_eq!(log.frontier,window==5||window==7);assert_eq!(log.length,if window==5||window==7{20}else if window==2||(withdrawal&&window==4){1}else{8});
 match got{Err(e)=>{assert!(fail);assert_eq!(e,error)},Ok(out)=>{assert!(!fail);assert_eq!(out.len(),11);assert_eq!(out[0],if withdrawal{1}else{0});assert_eq!(out[1],if withdrawal{0}else{1});assert_eq!(out[2],if withdrawal{1}else{0});let k:usize=kani::any();kani::assume(k<8);assert_eq!(out[k+3],((t.live_snapshot.next_pair_index>>(8*k))&255)as u8);}}
}

fn NHG_public_prefix(public:Public<'_>,log:&mut Log)->Result<alloc::vec::Vec<u8>,Error>{
            let p = public.semantic();
            let mut out = Vec::new();
            log.expected_owner=&out;
            out.push(match p.variant {
                CompiledVariant::PrivateTransfer => 0,
                CompiledVariant::Withdrawal => 1,
            });
            NHG_fields(&mut out, &p.anchor,log)?;
            NHG_fields(&mut out, &p.nullifier,log)?;
            NHG_fields(&mut out, &[p.asset_id],log)?;
            out.push(u8::from(p.recipient.is_some()));
            if let Some(value) = p.recipient {
                NHG_fields(&mut out, &value,log)?;
            }
            NHG_fields(&mut out, &p.change,log)?;
            out.push(u8::from(p.withdrawal_amount.is_some()));
            if let Some(value) = p.withdrawal_amount {
                NHG_fields(&mut out, &[M31(value)],log)?;
            }
            Ok(out)
}

#[kani::proof]#[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NHG_public_prefix_routing(){
 let p=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()};
 let w=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()};
 // Fully arbitrary typed transition: no zero/sparse prestate restriction.
 let t=PoolV1PairLatePublicStatementV1{
  live_snapshot:crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{
   pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:core::array::from_fn(|_|digest())},
  candidate_afterstate:crate::pool_v1::PoolV1PairVerifiedAfterstateV1{
   next_pair_index:kani::any(),next_root:digest(),next_frontier:core::array::from_fn(|_|digest())}};
 let withdrawal:bool=kani::any();let public=if withdrawal{Public::Withdrawal(&w,&t)}else{Public::Transfer(&p,&t)};

 let window:usize=kani::any();kani::assume(window<5);let row:usize=kani::any();kani::assume(row<20);let word:usize=kani::any();kani::assume(word<8);let fail:bool=kani::any();let error=any_error();
 let mut log=Log{expected_owner:core::ptr::null(),calls:0,window,fail,error,seen:false,frontier:false,row,word,value:0,length:0,owner:core::ptr::null()};
 if cfg!(NHG_invert){kani::assume(window==0);}
 let got=NHG_public_prefix(public,&mut log);assert!(log.seen);assert_eq!(log.calls,if fail{window+1}else{5});
 let expected=match window{0=>if withdrawal{w.anchor_root[word].0}else{p.anchor_root[word].0},1=>if withdrawal{w.nullifier[word].0}else{p.nullifier[word].0},2=>if withdrawal{w.asset_id.0}else{p.asset_id.0},3=>if withdrawal{w.change_commitment[word].0}else{p.recipient_commitment[word].0},4=>if withdrawal{w.amount}else{p.change_commitment[word].0},5=>t.live_snapshot.frontier[row][word].0,6=>t.candidate_afterstate.next_root[word].0,_=>t.candidate_afterstate.next_frontier[row][word].0};
 assert_eq!(log.value,expected^if cfg!(NHG_invert){1}else{0});assert_eq!(log.frontier,window==5||window==7);assert_eq!(log.length,if window==5||window==7{20}else if window==2||(withdrawal&&window==4){1}else{8});
 match got{Err(e)=>{assert!(fail);assert_eq!(e,error)},Ok(out)=>{assert!(!fail);assert_eq!(out.len(),3);assert_eq!(out[0],if withdrawal{1}else{0});assert_eq!(out[1],if withdrawal{0}else{1});assert_eq!(out[2],if withdrawal{1}else{0});}}
}
