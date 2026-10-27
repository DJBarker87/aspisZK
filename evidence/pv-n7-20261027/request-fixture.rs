use anyhow::{anyhow,Result};
use aspis_pool::{pool_v1_pair_forest_master_address,pool_v1_pair_forest_lane_address,pool_v1_pair_forest_checkpoint_address,POOL_V1_PAIR_EMPTY_ROOTS};
use aspis_statement::pool_v1::*;
use solana_program::pubkey::Pubkey;
use std::{fs,path::Path};
use serde_json::json;
fn checked<T,E:std::fmt::Debug>(r:std::result::Result<T,E>)->Result<T>{r.map_err(|e|anyhow!("{e:?}"))}
fn hex(b:&[u8])->String{b.iter().map(|x|format!("{x:02x}")).collect()}
fn digest(seed: u32) -> aspis_statement::poseidon2::Digest {
    core::array::from_fn(|i| {
        aspis_core::field::M31((seed + 17 * i as u32 + 1) % aspis_core::field::P)
    })
}
fn note(
    n: u32,
) -> (
    aspis_statement::poseidon2::Digest,
    aspis_statement::poseidon2::Digest,
    aspis_statement::poseidon2::Digest,
) {
    let mut found = 0;
    for j in 0..10000 {
        let k = digest(10 + j);
        let salt = digest(100 + j);
        let cm = pool_v1_note_commitment(
            &aspis_statement::derive_owner_key(&k),
            1000,
            aspis_core::field::M31(77),
            &salt,
        );
        let nf = pool_v1_nullifier(&k, &salt);
        if pool_v1_pair_forest_deposit_lane_v1(&cm).unwrap()
            == pool_v1_pair_forest_output_lane_v1(&nf).unwrap()
        {
            if found == n {
                return (k, salt, cm);
            }
            found += 1;
        }
    }
    panic!("fixture exhausted")
}
fn fixture(
    pool: Pubkey,
    mint: Pubkey,
    n: u32,
) -> Result<(
    Pubkey,
    Pubkey,
    Vec<u8>,
    Vec<u8>,
    Vec<aspis_statement::poseidon2::Digest>,
)> {
    let master = pool_v1_pair_forest_master_address(&pool, &mint).0;
    let mut trees: Vec<_> = (0..8)
        .map(|_| IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[20],
            frontier: core::array::from_fn(|i| POOL_V1_PAIR_EMPTY_ROOTS[i]),
        })
        .collect();
    let mut histories = vec![vec![POOL_V1_PAIR_EMPTY_ROOTS[20]]; 8];
    for j in 0..2 {
        let (_, _, cm) = note(j);
        let l = checked(pool_v1_pair_forest_deposit_lane_v1(&cm))? as usize;
        let leaf = checked(checked(PoolV1PairLeafWitnessV1::single_output(cm))?.leaf_digest())?;
        trees[l] =
            checked(trees[l].append_one_with_empty_roots(leaf, &POOL_V1_PAIR_EMPTY_ROOTS))?.0;
        histories[l].push(trees[l].root);
    }
    let mut roots: Vec<_> = trees.iter().map(|t| t.root).collect();
    while roots.len() > 1 {
        roots = roots
            .chunks(2)
            .map(|s| pool_v1_tree_parent(&s[0], &s[1]))
            .collect();
    }
    let (_, _, cm) = note(n);
    let l = checked(pool_v1_pair_forest_deposit_lane_v1(&cm))?;
    let (lane, bump) = checked(pool_v1_pair_forest_lane_address(&pool, &master, l))?;
    let (cp, cpb) = pool_v1_pair_forest_checkpoint_address(&pool, &master, 0);
    let lane_bytes = checked(encode_pool_v1_pair_forest_lane_state_v1(
        &PoolV1PairForestLaneStateV1 {
            bump,
            master: master.to_bytes(),
            lane_id: l,
            tree: trees[l as usize],
        },
        &POOL_V1_PAIR_EMPTY_ROOTS,
    ))?
    .to_vec();
    let cp_bytes = checked(encode_pool_v1_pair_forest_checkpoint_v1(
        &PoolV1PairForestCheckpointV1 {
            bump: cpb,
            master: master.to_bytes(),
            deployment_domain: [5; 32],
            checkpoint_sequence: 0,
            global_root: roots[0],
            lane_sequences: core::array::from_fn(|i| trees[i].next_leaf_index),
        },
    ))?
    .to_vec();
    Ok((
        lane,
        cp,
        lane_bytes,
        cp_bytes,
        histories[l as usize].clone(),
    ))
}

fn main()->Result<()> {
 let args:Vec<_>=std::env::args().collect();let out=Path::new(&args[1]);fs::create_dir(out)?;
 let pool=Pubkey::new_from_array([0x41;32]);let mint=Pubkey::new_from_array([0x42;32]);
 for n in 0..2 {
  let (_,cp,lb,cb,_)=fixture(pool,mint,n)?;
  let q=json!({"action":"prove","pool":pool.to_string(),"mint":mint.to_string(),"payer":Pubkey::new_from_array([0x43;32]).to_string(),"registry":Pubkey::new_from_array([0x44;32]).to_string(),"verifier":Pubkey::new_from_array([0x45;32]).to_string(),"note":n,"withdrawal":n==1,"destination":Pubkey::new_from_array([0x49;32]).to_string(),"checkpoint":cp.to_string(),"lane_bytes":hex(&lb),"checkpoint_bytes":hex(&cb),"proof_accounts":(1..=8).map(|i|Pubkey::new_from_array([i;32]).to_string()).collect::<Vec<_>>(),"public_account":Pubkey::new_from_array([0x50;32]).to_string(),"verifier_checkpoint":Pubkey::new_from_array([0x51;32]).to_string()});
  fs::write(out.join(format!("request-{n}.json")),serde_json::to_vec_pretty(&q)?)?;
 }Ok(())
}
