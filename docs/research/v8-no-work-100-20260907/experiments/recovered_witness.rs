//! Executable tuple-to-witness endpoint, given recovered canonical C1
//! coefficients in the selected direct message-table convention.
//! It reads source trace cells and calls the actual witness/compiler validator.
//! It does not assume that proof acceptance yields these coefficients.
extern crate aspis_core as corelib;
extern crate aspis_statement as statement;
use corelib::field::M31;
use statement::{derive_owner_key,poseidon2::Digest,state_only_trace::StateOnlyTraceFoundation};
use statement::pool_v1::*;
use statement::pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1;
use statement::pool_v1::pair_forest_hiding::{pool_v1_pair_forest_path_base_row_v1 as path,
    POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1 as OCC};
fn dig(s:u32)->Digest{std::array::from_fn(|j|M31(s+17*j as u32+1))}
fn context(p:&PoolV1PrivateTransferPublicV1)->PoolV1PaymentRelationContextV1<'_>{
    PoolV1PaymentRelationContextV1{runtime_binding:PoolV1PaymentRuntimeBindingV1{
        pool:p.pool,deployment_domain:p.deployment_domain,anchor_sequence:p.anchor_sequence,
        anchor_root:p.anchor_root,asset_id:p.asset_id},spent_nullifiers:&[]}
}
fn fixture()->(PoolV1PrivateTransferPublicV1,PoolV1PairForestPrivateTransferWitnessV1,PoolV1PairLiveSnapshotV1){
    let key=dig(10);let salt=dig(100);let asset=M31(77);
    let leaf=pool_v1_note_commitment(&derive_owner_key(&key),1000,asset,&salt);
    let pair=PoolV1PairLeafWitnessV1::two_outputs(leaf,dig(900)).unwrap();
    let input=PoolV1PairForestInputNoteWitnessV1{pair:PoolV1PairInputNoteWitnessV1{
        nullifier_key:key,salt,value:1000,pair_leaf:pair,selected_second:false,
        membership:PoolV1MembershipWitnessV1{siblings:std::array::from_fn(|i|dig(2000+20*i as u32)),index:0x54321}},
        super_root_siblings:[dig(3000),dig(3100),dig(3200)],super_root_directions:[true,false,true]};
    let mut root=pair.leaf_digest().unwrap();
    for i in 0..20{let sibling=input.pair.membership.siblings[i];root=if (input.pair.membership.index>>i)&1==0{
        pool_v1_tree_parent(&root,&sibling)}else{pool_v1_tree_parent(&sibling,&root)};}
    for i in 0..3{let sibling=input.super_root_siblings[i];root=if input.super_root_directions[i]{
        pool_v1_tree_parent(&sibling,&root)}else{pool_v1_tree_parent(&root,&sibling)};}
    let recipient=PoolV1OutputNoteWitnessV1{owner_key:dig(300),salt:dig(400),value:600};
    let change=PoolV1OutputNoteWitnessV1{owner_key:dig(500),salt:dig(600),value:400};
    let public=PoolV1PrivateTransferPublicV1{pool:[1;32],deployment_domain:[2;32],anchor_sequence:42,
        anchor_root:root,nullifier:pool_v1_nullifier(&key,&salt),asset_id:asset,
        recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,recipient.value,asset,&recipient.salt),
        change_commitment:pool_v1_note_commitment(&change.owner_key,change.value,asset,&change.salt)};
    let mut empty=[[M31::ZERO;8];21];empty[0]=pool_v1_tree_parent(&[M31::ZERO;8],&[M31::ZERO;8]);
    for i in 1..21{empty[i]=pool_v1_tree_parent(&empty[i-1],&empty[i-1]);}
    let snapshot=PoolV1PairLiveSnapshotV1{pool:public.pool,deployment_domain:public.deployment_domain,
        sequence:0,next_pair_index:0,current_root:empty[20],frontier:std::array::from_fn(|i|empty[i])};
    (public,PoolV1PairForestPrivateTransferWitnessV1{input,recipient,change},snapshot)
}
fn decode(c:&StateOnlyTraceFoundation)->Result<PoolV1PairForestPrivateTransferWitnessV1,&'static str>{
    if c.c1.iter().any(|x|x.len()!=1024||x.iter().any(|v|v.0>=corelib::field::P)){return Err("shape/canonical");}
    let get=|row:usize,col:usize|c.c1[col][row];
    let digest=|row:usize,start:usize|std::array::from_fn(|i|get(row,start+i));
    let bit=|level:usize|->Result<bool,&'static str>{match get(path(level).ok_or("path")?,0).0{
        0=>Ok(false),1=>Ok(true),_=>Err("nonboolean direction")}};
    let sibling=|level:usize|->Result<Digest,&'static str>{
        Ok(digest(path(level).ok_or("path")?+1,if bit(level)?{0}else{8}))
    };
    let note=|block:usize|PoolV1OutputNoteWitnessV1{
        owner_key:digest(16*block+12,0),value:get(16*(block+1)+12,0).0,
        salt:std::array::from_fn(|i|if i<6{get(16*(block+1)+12,i+2)}else{get(16*(block+2)+12,i-6)})};
    let selected=bit(0)?;let row=path(0).unwrap()+1;
    let pair_leaf=PoolV1PairLeafWitnessV1{first_commitment:digest(row,0),second_commitment:digest(row,8),
        second_occupied:get(OCC,0),second_occupancy_inverse:get(OCC,1)};
    pair_leaf.validate().map_err(|_|"pair occupancy")?;
    let mut index=0;let mut siblings=[[M31::ZERO;8];20];
    for i in 0..20{index|=(bit(i+1)? as u32)<<i;siblings[i]=sibling(i+1)?;}
    let mut super_root_siblings=[[M31::ZERO;8];3];let mut super_root_directions=[false;3];
    for i in 0..3{super_root_siblings[i]=sibling(i+21)?;super_root_directions[i]=bit(i+21)?;}
    let input_note=note(1);
    Ok(PoolV1PairForestPrivateTransferWitnessV1{input:PoolV1PairForestInputNoteWitnessV1{
        pair:PoolV1PairInputNoteWitnessV1{nullifier_key:digest(12,0),salt:input_note.salt,
            value:input_note.value,pair_leaf,selected_second:selected,
            membership:PoolV1MembershipWitnessV1{siblings,index}},
        super_root_siblings,super_root_directions},recipient:note(27),change:note(30)})
}
fn extract_checked(c:&StateOnlyTraceFoundation,p:&PoolV1PrivateTransferPublicV1,
    transition:&PoolV1PairLatePublicStatementV1,ctx:PoolV1PaymentRelationContextV1<'_>)->Result<PoolV1PairForestPrivateTransferWitnessV1,&'static str>{
    // Bind the OUTER forest root before the compiler substitutes its temporary
    // lane-root context. The authenticated context is supplied by the caller.
    if ctx.runtime_binding!=context(p).runtime_binding{return Err("runtime binding");}
    let w=decode(c)?;
    // This is a checked value returned by a real validator call, not a
    // PaymentWitness type fabricated from an assumed validWitness predicate.
    let compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        p,&w,ctx,transition.live_snapshot).map_err(|_|"payment validation")?;
    if compiled.public_statement!=*transition{return Err("settlement transition");}
    Ok(w)
}
fn main(){
    let(p,w,s)=fixture();
    let c=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&p,&w,context(&p),s).unwrap();
    let residuals=statement::pool_v1::pair_forest_constraint_residuals::
        evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(&p,&c.public_statement,&c.semantic_c1).unwrap();
    assert!(residuals.all_zero());
    let start=std::time::Instant::now();
    for _ in 0..100{assert_eq!(extract_checked(&c.semantic_c1,&p,&c.public_statement,context(&p)).unwrap(),w);}
    let elapsed=start.elapsed().as_secs_f64();
    // The source's relation-free masking cells must not supply any decoded
    // witness coordinate. This tests one fully populated mask assignment;
    // it is not a full-view privacy/rank theorem.
    let mask_cells=statement::pool_v1::pair_forest_hiding::
        pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let mut masked=c.semantic_c1.clone();
    for (i,cell) in mask_cells.iter().enumerate(){
        masked.c1[cell.column as usize][cell.row as usize]=M31(i as u32+1);
    }
    assert_eq!(extract_checked(&masked,&p,&c.public_statement,context(&p)).unwrap(),w);
    let mut masked_residuals=statement::pool_v1::pair_forest_constraint_residuals::
        evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(
            &p,&c.public_statement,&masked).unwrap();
    // This host evaluator deliberately includes a zero-padding class;
    // populated masks do not satisfy that class. No masked all_zero claim.
    assert!(masked_residuals.zero_padding.iter().all(|v|*v!=M31::ZERO));
    masked_residuals.zero_padding.fill(M31::ZERO);
    assert!(masked_residuals.all_zero());
    let mut rejected=0;
    for (row,col) in [(12,0),(44,2),(444,0),(460,0),(492,0),(path(5).unwrap()+1,8)]{
        let mut corrupt=c.semantic_c1.clone();corrupt.c1[col][row]=corrupt.c1[col][row].add(M31::ONE);
        assert!(extract_checked(&corrupt,&p,&c.public_statement,context(&p)).is_err());rejected+=1;
    }
    let mut corrupt=c.semantic_c1.clone();corrupt.c1[0][path(1).unwrap()]=M31(2);
    assert!(extract_checked(&corrupt,&p,&c.public_statement,context(&p)).is_err());rejected+=1;
    let mut public=p;public.asset_id=public.asset_id.add(M31::ONE);
    assert!(extract_checked(&c.semantic_c1,&public,&c.public_statement,context(&p)).is_err());rejected+=1;
    let mut tr=c.public_statement;tr.candidate_afterstate.next_pair_index+=1;
    assert!(extract_checked(&c.semantic_c1,&p,&tr,context(&p)).is_err());rejected+=1;
    let spent=[p.nullifier];let mut ctx=context(&p);ctx.spent_nullifiers=&spent;
    assert!(extract_checked(&c.semantic_c1,&p,&c.public_statement,ctx).is_err());rejected+=1;
    let mut ctx=context(&p);ctx.runtime_binding.deployment_domain[0]^=1;
    assert!(extract_checked(&c.semantic_c1,&p,&c.public_statement,ctx).is_err());rejected+=1;
    let mut ctx=context(&p);ctx.runtime_binding.anchor_root[0]=ctx.runtime_binding.anchor_root[0].add(M31::ONE);
    assert!(extract_checked(&c.semantic_c1,&p,&c.public_statement,ctx).is_err());rejected+=1;
    let mut corrupt=c.semantic_c1.clone();corrupt.c1[0].pop();
    assert!(extract_checked(&corrupt,&p,&c.public_statement,context(&p)).is_err());rejected+=1;
    let mut corrupt=c.semantic_c1.clone();corrupt.c1[0][0]=M31(corelib::field::P);
    assert!(extract_checked(&corrupt,&p,&c.public_statement,context(&p)).is_err());rejected+=1;
    println!("PASS checked_transfer_extractions=100 mutations_rejected={rejected} populated_mask_cells={} source_residuals={} extraction_100_seconds={elapsed}",mask_cells.len(),residuals.residual_count());
    println!("SCOPE deterministic recovered-C1-to-checked-transfer-witness endpoint; fixture equality, not a universal proof of extraction from acceptance. No secrets printed.");
}
