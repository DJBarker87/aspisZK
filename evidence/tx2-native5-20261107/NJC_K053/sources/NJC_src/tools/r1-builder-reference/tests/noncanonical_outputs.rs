//! Admission probe using the unchanged D70 fixed-fixture helpers.
use aspis_core::field::{M31, P};
use aspis_statement::{
    derive_owner_key,
    poseidon2::Digest,
    pool_v1::{
        pair_forest_trace::{
            compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
            compile_pool_v1_pair_forest_withdrawal_merged_c1_v1, PoolV1PairForestInputNoteWitnessV1,
            PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestWithdrawalWitnessV1,
        },
        pair_trace::PoolV1PairInputNoteWitnessV1,
        pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent, IncrementalMerkleTreeV1,
        PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1, PoolV1PairLeafWitnessV1,
        PoolV1PairLiveSnapshotV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1, POOL_V1_PAIR_TREE_DEPTH,
    },
};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn m31(&mut self) -> u32 {
        self.below(P as u64) as u32
    }
    fn digest(&mut self) -> Digest {
        core::array::from_fn(|_| M31(self.m31()))
    }
}

fn raw(d: &Digest) -> [u32; 8] {
    core::array::from_fn(|i| d[i].0)
}

fn context<'a>(pool: [u8; 32], dom: [u8; 32], anchor: Digest, asset: M31) -> PoolV1PaymentRelationContextV1<'a> {
    PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool,
            deployment_domain: dom,
            anchor_sequence: 42,
            anchor_root: anchor,
            asset_id: asset,
        },
        spent_nullifiers: &[],
    }
}

fn digest_seed(seed: u32) -> Digest {
    core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
}

fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
    let zero = [M31(0); 8];
    let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
    roots[0] = pool_v1_tree_parent(&zero, &zero);
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
    }
    roots
}

fn snapshot_at(pool: [u8; 32], dom: [u8; 32], index: u64) -> PoolV1PairLiveSnapshotV1 {
    let empty = pair_empty_roots();
    let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
        0, empty[POOL_V1_PAIR_TREE_DEPTH], core::array::from_fn(|level| empty[level]), &empty).unwrap();
    for leaf in 0..index {
        tree = tree.append_one_with_empty_roots(digest_seed(20_000 + 32 * leaf as u32), &empty).unwrap().0;
    }
    PoolV1PairLiveSnapshotV1 {
        pool,
        deployment_domain: dom,
        sequence: index,
        next_pair_index: index,
        current_root: tree.root,
        frontier: tree.frontier,
    }
}

/// The saved fixture (pool_v1_pair_forest_honest.rs tests) when `rng` is None,
/// otherwise a randomized witness of the same shape.
fn input_witness(value: u32, rng: Option<&mut Rng>) -> PoolV1PairForestInputNoteWitnessV1 {
    let asset = M31(77);
    match rng {
        None => {
            let nullifier_key = digest_seed(10);
            let salt = digest_seed(100);
            let owner = derive_owner_key(&nullifier_key);
            let c = pool_v1_note_commitment(&owner, value, asset, &salt);
            PoolV1PairForestInputNoteWitnessV1 {
                pair: PoolV1PairInputNoteWitnessV1 {
                    nullifier_key,
                    salt,
                    value,
                    pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(c, digest_seed(900)).unwrap(),
                    selected_second: false,
                    membership: PoolV1MembershipWitnessV1 {
                        siblings: core::array::from_fn(|level| digest_seed(2_000 + 20 * level as u32)),
                        index: 0x5_4321,
                    },
                },
                super_root_siblings: [digest_seed(3_000), digest_seed(3_100), digest_seed(3_200)],
                super_root_directions: [true, false, true],
            }
        }
        Some(rng) => {
            let nullifier_key = rng.digest();
            let salt = rng.digest();
            let owner = derive_owner_key(&nullifier_key);
            let c = pool_v1_note_commitment(&owner, value, asset, &salt);
            let mut other = rng.digest();
            if other[7].0 == 0 {
                other[7] = M31(1);
            }
            let selected_second = rng.below(2) == 1;
            let pair_leaf = if selected_second {
                PoolV1PairLeafWitnessV1::two_outputs(other, c).unwrap()
            } else if rng.below(2) == 1 {
                PoolV1PairLeafWitnessV1::two_outputs(c, other).unwrap()
            } else {
                PoolV1PairLeafWitnessV1::single_output(c).unwrap()
            };
            PoolV1PairForestInputNoteWitnessV1 {
                pair: PoolV1PairInputNoteWitnessV1 {
                    nullifier_key,
                    salt,
                    value,
                    pair_leaf,
                    selected_second,
                    membership: PoolV1MembershipWitnessV1 {
                        siblings: core::array::from_fn(|_| rng.digest()),
                        index: rng.below(1 << 20) as u32,
                    },
                },
                super_root_siblings: [rng.digest(), rng.digest(), rng.digest()],
                super_root_directions: core::array::from_fn(|_| rng.below(2) == 1),
            }
        }
    }
}

fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
    let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        let s = input.pair.membership.siblings[level];
        current = if ((input.pair.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &s)
        } else {
            pool_v1_tree_parent(&s, &current)
        };
    }
    for level in 0..3 {
        let s = input.super_root_siblings[level];
        current = if input.super_root_directions[level] {
            pool_v1_tree_parent(&s, &current)
        } else {
            pool_v1_tree_parent(&current, &s)
        };
    }
    current
}


#[test]
fn successful_compile_accepts_noncanonical_recipient_owner() {
    let input=input_witness(1_000,None);
    let asset=M31(77); let anchor=global_anchor(&input);
    let snapshot=snapshot_at([1;32],[2;32],13);
    let recipient=PoolV1OutputNoteWitnessV1 { owner_key:digest_seed(300),salt:digest_seed(400),value:600 };
    let change=PoolV1OutputNoteWitnessV1 { owner_key:digest_seed(500),salt:digest_seed(600),value:400 };
    let public=PoolV1PrivateTransferPublicV1 { pool:[1;32],deployment_domain:[2;32],anchor_sequence:42,
        anchor_root:anchor,nullifier:pool_v1_nullifier(&input.pair.nullifier_key,&input.pair.salt),asset_id:asset,
        recipient_commitment:pool_v1_note_commitment(&recipient.owner_key,600,asset,&recipient.salt),
        change_commitment:pool_v1_note_commitment(&change.owner_key,400,asset,&change.salt) };
    let mut witness=PoolV1PairForestPrivateTransferWitnessV1 { input,recipient,change };
    let original=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,
        context(public.pool,public.deployment_domain,anchor,asset),snapshot).expect("canonical fixture");
    witness.recipient.owner_key[0].0 += P;
    assert!(witness.recipient.owner_key[0].0 >= P);
    let changed=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&witness,
        context(public.pool,public.deployment_domain,anchor,asset),snapshot).expect("noncanonical owner accepted");
    assert_eq!(changed.semantic_c1.c1[0][27*16+12].0,witness.recipient.owner_key[0].0);
    assert_ne!(changed.semantic_c1.c1[0][27*16+12],original.semantic_c1.c1[0][27*16+12]);
    for c in 0..16 { for r in 0..1024 {
        assert_eq!(changed.semantic_c1.c1[c][r].0 % P,original.semantic_c1.c1[c][r].0 % P);
    } }
}
