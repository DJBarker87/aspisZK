//! Research-only selected semantic/validator mismatch diagnostic.
//! No proof is generated or submitted. Every witness is synthetic; no secret
//! field, witness, or note commitment is printed.
extern crate aspis_core as corelib;
extern crate aspis_statement as statement;

#[path = "recovered_witness.rs"]
mod recovered;

use corelib::field::{CM31, M31, QM31};
use statement::pool_v1::*;
use statement::pool_v1::pair_trace::PoolV1PairTraceErrorV1;
use statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1;
use statement::pool_v1::pair_forest_semantic_terminal::
    evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1 as terminal;
use statement::poseidon2::{Digest, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_ROUNDS,
    permute_optimized_with_trace};

fn lift(x: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(x)) }

// Mirrors pair_trace::write_permutation. It calls the literal public
// permutation kernel, retains every odd-round output, and writes the same
// pre-absorption and chunk cells. No constraint is relaxed.
fn permutation(c: &mut [Vec<M31>; 16], block: usize, pre: [M31; 16], chunk: Digest)
    -> [M31; 16]
{
    assert!(block < 54);
    let base = 16 * block;
    for col in c.iter_mut() { col[base..base+16].fill(M31::ZERO); }
    for i in 0..16 { c[i][base] = pre[i]; }
    for i in 0..8 { c[i][base+12] = chunk[i]; }
    let mut state = pre;
    for i in 0..8 { state[i] = state[i].add(chunk[i]); }
    let mut rounds = 0;
    permute_optimized_with_trace(&mut state, |r| {
        rounds += 1;
        if r.round & 1 == 1 {
            let row = base + usize::from(r.round)/2 + 1;
            for i in 0..16 { c[i][row] = r.output[i]; }
        }
    });
    assert_eq!(rounds, POSEIDON2_ROUNDS);
    state
}

fn note(c: &mut [Vec<M31>; 16], block: usize, n: PoolV1OutputNoteWitnessV1, asset: M31)
    -> Digest
{
    let mut input = [M31::ZERO; 18];
    input[..8].copy_from_slice(&n.owner_key);
    input[8] = M31(n.value); input[9] = asset;
    input[10..].copy_from_slice(&n.salt);
    // Exact hash_fields_with_trace initial capacity and three rate-8 chunks.
    let mut state = [M31::ZERO; 16];
    // spend::DOMAIN_NOTE is crate-private; literal pinned value, independently
    // checked below against the public note hash on every constructed note.
    state[8] = M31(0x4153_0003); state[9] = M31(18);
    for (i, raw) in input.chunks(8).enumerate() {
        let mut chunk = [M31::ZERO; 8];
        chunk[..raw.len()].copy_from_slice(raw);
        state = permutation(c, block+i, state, chunk);
    }
    let out = std::array::from_fn(|i| state[i]);
    assert_eq!(out, pool_v1_note_commitment(&n.owner_key,n.value,asset,&n.salt));
    out
}

fn node(c: &mut [Vec<M31>; 16], block: usize, left: Digest, right: Digest) -> Digest {
    let mut pre = [M31::ZERO; 16]; pre[8..].copy_from_slice(&right);
    pre[15] = pre[15].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    let state = permutation(c, block, pre, left);
    let out = std::array::from_fn(|i| state[i]);
    assert_eq!(out, pool_v1_tree_parent(&left,&right));
    out
}

fn value_rows(c: &mut [Vec<M31>; 16], values: [u32; 3]) {
    // Exact forest relocation of legacy 960..967 and XOR12 bit rows.
    for (i, raw) in values.into_iter().enumerate() {
        let base = 1008 + 2*i;
        for bit in 0..30 {
            let row = if bit<10 {base} else if bit<20 {base+1} else {base^12};
            c[bit%10][row] = M31((raw>>bit)&1);
        }
        c[10][base] = M31(raw);
        // The selected terminal additionally enforces these six zeros.
        assert_eq!(c[10][base+1],M31::ZERO);
        assert_eq!(c[10][base^12],M31::ZERO);
    }
    let partial = M31(values[0]).sub(M31(values[1]));
    c[0][1014]=M31(values[0]); c[1][1014]=M31(values[1]); c[2][1014]=partial;
    c[0][1015]=partial; c[1][1015]=M31(values[2]);
}

pub(crate) fn rewrite_outputs(baseline: &PoolV1PairForestMergedC1CompilationV1,
    mut public: PoolV1PrivateTransferPublicV1,
    w: PoolV1PairForestPrivateTransferWitnessV1)
    -> (PoolV1PrivateTransferPublicV1, PoolV1PairForestMergedC1CompilationV1)
{
    let mut c = baseline.clone();
    let r = note(&mut c.trace.stable.c1,27,w.recipient,public.asset_id);
    let ch = note(&mut c.trace.stable.c1,30,w.change,public.asset_id);
    public.recipient_commitment=r; public.change_commitment=ch;
    let pair = PoolV1PairLeafWitnessV1::two_outputs(r,ch).unwrap();
    let output = node(&mut c.trace.stable.c1,33,r,ch);
    value_rows(&mut c.trace.stable.c1,[w.input.pair.value,w.recipient.value,w.change.value]);
    c.trace.stable.c1[0][1018]=pair.second_occupied;
    c.trace.stable.c1[1][1018]=pair.second_occupancy_inverse;
    for i in 0..8 { c.trace.stable.c1[i+2][1018]=ch[i]; }
    let snapshot = c.public_statement.live_snapshot;
    let mut empty = [[M31::ZERO;8];21];
    empty[0]=pool_v1_tree_parent(&[M31::ZERO;8],&[M31::ZERO;8]);
    for i in 0..20 { empty[i+1]=pool_v1_tree_parent(&empty[i],&empty[i]); }
    let tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
        snapshot.next_pair_index,snapshot.current_root,snapshot.frontier,&empty).unwrap();
    let (next,_) = tree.append_one_with_empty_roots(output,&empty).unwrap();
    let mut current = output;
    for i in 0..20 {
        let right = ((snapshot.next_pair_index>>i)&1)==1;
        let sibling = if right {snapshot.frontier[i]} else {empty[i]};
        current = if right {node(&mut c.trace.late,34+i,sibling,current)}
            else {node(&mut c.trace.late,34+i,current,sibling)};
    }
    assert_eq!(current,next.root);
    c.trace.afterstate=PoolV1PairVerifiedAfterstateV1 {
        next_pair_index:next.next_leaf_index,next_root:next.root,next_frontier:next.frontier};
    c.trace.public_outputs=statement::pool_v1::pair_trace::PoolV1PairTracePublicOutputsV1::PrivateTransfer {
        anchor:public.anchor_root,nullifier:public.nullifier,recipient_commitment:r,
        change_commitment:ch,output_pair:output};
    c.trace.value_bits=std::array::from_fn(|j|std::array::from_fn(|bit|
        M31(([w.input.pair.value,w.recipient.value,w.change.value][j]>>bit)&1)));
    c.semantic_c1=merge_pool_v1_pair_forest_trace_banks_v1(&c.trace).unwrap();
    c.public_statement.candidate_afterstate=c.trace.afterstate;
    // Preserve every input, key, path and forest cell, not merely their hashes.
    for i in 0..16 {
        assert_eq!(c.semantic_c1.c1[i][..432],baseline.semantic_c1.c1[i][..432]);
        assert_eq!(c.semantic_c1.c1[i][864..1008],baseline.semantic_c1.c1[i][864..1008]);
        assert_eq!(c.semantic_c1.c1[i][1017],baseline.semantic_c1.c1[i][1017]);
    }
    (public,c)
}

fn check_all_selected(public: &PoolV1PrivateTransferPublicV1,
    c: &PoolV1PairForestMergedC1CompilationV1) -> (usize,usize)
{
    let residuals=statement::pool_v1::pair_forest_constraint_residuals::
        evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1(
            public,&c.public_statement,&c.semantic_c1).unwrap();
    // Keep all 18,089 entries, including all 3,803 zero-padding entries.
    assert_eq!(residuals.residual_count(),18_089);
    assert_eq!(residuals.zero_padding.len(),3_803);
    assert!(residuals.all_zero(),"one or more literal residuals nonzero");
    let lambda=QM31 {c0:CM31 {a:M31(11),b:M31(13)},c1:CM31 {a:M31(17),b:M31(19)}};
    let chi=QM31 {c0:CM31 {a:M31(31),b:M31(37)},c1:CM31 {a:M31(41),b:M31(43)}};
    let theta=QM31 {c0:CM31 {a:M31(47),b:M31(53)},c1:CM31 {a:M31(59),b:M31(61)}};
    // Fixed predeclared probes, no retries/selection. Helper failure is fatal.
    let h=statement::pool_v1::pair_forest_semantic_oracle::
        build_pool_v1_pair_forest_copy_helper_v1(&c.trace,
            c.public_statement.live_snapshot.next_pair_index,lambda,chi).unwrap();
    assert_eq!(statement::state_only_copy_helper_sum(&h),Some(QM31::ZERO));
    for row in 0..1024 {
        let rows=[row,(row+1)&1023,row^12];
        let point=std::array::from_fn(|j|lift(M31(((row>>(9-j))&1)as u32)));
        let claims=std::array::from_fn(|i| {
            let col=i%28; let r=rows[i/28];
            if col<16 {lift(c.semantic_c1.c1[col][r])}
            else if col==26 {h[r]} else {QM31::ZERO}
        });
        assert_eq!(terminal(public,&c.public_statement,&claims,&point,lambda,chi,theta).unwrap(),
            QM31::ZERO,"selected Boolean composition at row {row}");
    }
    (residuals.residual_count(),1024)
}

fn main() {
    let (p,w,s)=recovered::fixture();
    let baseline=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &p,&w,recovered::context(&p),s).unwrap();
    // Inventory only, not installed: one inverse at row1014/column3 would
    // allow a new cubic residual r*c*u-1 at the existing conservation row.
    let masks=statement::pool_v1::pair_forest_hiding::
        pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    assert!(masks.iter().any(|cell|cell.row==1014 && cell.column==3));
    let product=M31(w.recipient.value).mul(M31(w.change.value));
    assert_eq!(product.mul(product.inv()),M31::ONE);
    for u in [M31::ZERO,M31::ONE,M31(7),M31(corelib::field::P-1)] {
        assert_eq!(M31::ZERO.mul(M31(1000)).mul(u).sub(M31::ONE),M31::ZERO.sub(M31::ONE));
    }
    let (rp,roundtrip)=rewrite_outputs(&baseline,p,w);
    assert_eq!(rp,p); assert_eq!(roundtrip,baseline);
    let (residuals,rows)=check_all_selected(&p,&baseline);
    assert!(recovered::extract_checked(&baseline.semantic_c1,&p,&baseline.public_statement,
        recovered::context(&p)).is_ok());
    println!("baseline=valid rewritten_trace_exact=true all_zero_residuals={residuals} compiled_boolean_rows={rows}");
    for (name,rv,cv) in [("recipient_zero",0,1000),("change_zero",1000,0)] {
        let mut zero_w=w; zero_w.recipient.value=rv; zero_w.change.value=cv;
        let (zp,z)=rewrite_outputs(&baseline,p,zero_w);
        validate_pool_v1_private_transfer_public_v1(&zp).unwrap();
        let (residuals,rows)=check_all_selected(&zp,&z);
        let decoded=recovered::decode(&z.semantic_c1).unwrap();
        assert_eq!(decoded,zero_w); // Assertion only, not decoder definition.
        assert!(matches!(compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
            &zp,&decoded,recovered::context(&zp),s),Err(PoolV1PairTraceErrorV1::Conservation)));
        assert_eq!(recovered::extract_checked(&z.semantic_c1,&zp,&z.public_statement,
            recovered::context(&zp)).unwrap_err(),"payment validation");
        println!("case={name} public_valid=true all_zero_residuals={residuals} compiled_boolean_rows={rows} decode_ok=true validator=Conservation extracted_checked=reject");
    }
    println!("SCOPE synthetic unmasked semantic-table counterexamples; no PCS/FS/complete transaction acceptance or absence-of-another-witness claim. No secrets printed.");
}
