//! Native differential gate of the writer migration (LOG D68.2).
//!
//! The shipped forest compiler (`compile_pool_v1_pair_forest_*_merged_c1_v1`,
//! every C1 cell written by the extracted copies) is compared with the retained
//! pre-migration compiler (`pair_forest_trace::reference`, the legacy writers
//! plus relocation) on the whole `Result`: on success every field of the
//! compilation (both banks, the merged semantic C1, directions, value bits,
//! public outputs, afterstate, public statement); on failure the exact error.
//! Witnesses: the two saved fixtures, the 512 randomized honest witnesses of
//! refine/diffharness/tests/glue.rs (same generator and seed), and 31 witness,
//! public, context and snapshot mutations of the fixtures and of the first 64
//! randomized witnesses, which exercise the error paths in order.
use std::collections::BTreeMap;

use aspis_core::field::{M31, P};
use aspis_statement::{
    derive_owner_key,
    poseidon2::Digest,
    pool_v1::{
        pair_forest_trace::{
            compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
            compile_pool_v1_pair_forest_withdrawal_merged_c1_v1, reference,
            PoolV1PairForestInputNoteWitnessV1, PoolV1PairForestMergedC1CompilationV1,
            PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestWithdrawalWitnessV1,
        },
        pair_trace::{PoolV1PairInputNoteWitnessV1, PoolV1PairTraceErrorV1},
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

/// glue.rs `input_witness`: the saved fixture when `rng` is None.
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

#[derive(Clone)]
enum Stmt {
    Transfer(PoolV1PrivateTransferPublicV1, PoolV1PairForestPrivateTransferWitnessV1),
    Withdrawal(PoolV1WithdrawalPublicV1, PoolV1PairForestWithdrawalWitnessV1),
}

#[derive(Clone)]
struct Case {
    stmt: Stmt,
    binding: PoolV1PaymentRuntimeBindingV1,
    spent: Vec<Digest>,
    snapshot: PoolV1PairLiveSnapshotV1,
}

type Out = Result<PoolV1PairForestMergedC1CompilationV1, PoolV1PairTraceErrorV1>;

impl Case {
    fn run(&self) -> (Out, Out) {
        let context = PoolV1PaymentRelationContextV1 { runtime_binding: self.binding, spent_nullifiers: &self.spent };
        match &self.stmt {
            Stmt::Transfer(public, witness) => (
                compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(public, witness, context, self.snapshot),
                reference::compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(public, witness, context, self.snapshot),
            ),
            Stmt::Withdrawal(public, witness) => (
                compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(public, witness, context, self.snapshot),
                reference::compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(public, witness, context, self.snapshot),
            ),
        }
    }
    fn input(&mut self) -> &mut PoolV1PairForestInputNoteWitnessV1 {
        match &mut self.stmt {
            Stmt::Transfer(_, w) => &mut w.input,
            Stmt::Withdrawal(_, w) => &mut w.input,
        }
    }
    fn change(&mut self) -> &mut PoolV1OutputNoteWitnessV1 {
        match &mut self.stmt {
            Stmt::Transfer(_, w) => &mut w.change,
            Stmt::Withdrawal(_, w) => &mut w.change,
        }
    }
    fn anchor(&mut self) -> &mut Digest {
        match &mut self.stmt {
            Stmt::Transfer(p, _) => &mut p.anchor_root,
            Stmt::Withdrawal(p, _) => &mut p.anchor_root,
        }
    }
    fn nullifier(&mut self) -> &mut Digest {
        match &mut self.stmt {
            Stmt::Transfer(p, _) => &mut p.nullifier,
            Stmt::Withdrawal(p, _) => &mut p.nullifier,
        }
    }
    fn change_commitment(&mut self) -> &mut Digest {
        match &mut self.stmt {
            Stmt::Transfer(p, _) => &mut p.change_commitment,
            Stmt::Withdrawal(p, _) => &mut p.change_commitment,
        }
    }
    fn asset(&mut self) -> &mut M31 {
        match &mut self.stmt {
            Stmt::Transfer(p, _) => &mut p.asset_id,
            Stmt::Withdrawal(p, _) => &mut p.asset_id,
        }
    }
}

/// glue.rs `build`, keeping the case even when production rejects it.
fn honest(mut rng: Option<&mut Rng>, transfer: bool) -> Case {
    let randomized = rng.is_some();
    let (input_value, part, index) = match rng.as_deref_mut() {
        Some(r) => {
            let v = 2 + r.below((1 << 30) - 2) as u32;
            (v, 1 + r.below(v as u64 - 1) as u32, r.below(64))
        }
        None => (1_000, if transfer { 600 } else { 250 }, 13),
    };
    let input = match rng.as_deref_mut() { Some(r) => input_witness(input_value, Some(r)), None => input_witness(input_value, None) };
    let asset = M31(77);
    let anchor = global_anchor(&input);
    let snapshot = snapshot_at([1; 32], [2; 32], index);
    let nullifier = pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt);
    let mut fresh = || -> Digest { match rng.as_deref_mut() { Some(r) => r.digest(), None => unreachable!() } };
    let binding = PoolV1PaymentRuntimeBindingV1 { pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor, asset_id: asset };
    let stmt = if transfer {
        let (rec, chg) = if randomized {
            (PoolV1OutputNoteWitnessV1 { owner_key: fresh(), salt: fresh(), value: part },
             PoolV1OutputNoteWitnessV1 { owner_key: fresh(), salt: fresh(), value: input_value - part })
        } else {
            (PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(300), salt: digest_seed(400), value: 600 },
             PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(500), salt: digest_seed(600), value: 400 })
        };
        let rc = pool_v1_note_commitment(&rec.owner_key, rec.value, asset, &rec.salt);
        let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier, asset_id: asset, recipient_commitment: rc, change_commitment: cc,
        };
        Stmt::Transfer(public, PoolV1PairForestPrivateTransferWitnessV1 { input, recipient: rec, change: chg })
    } else {
        let chg = if randomized {
            PoolV1OutputNoteWitnessV1 { owner_key: fresh(), salt: fresh(), value: input_value - part }
        } else {
            PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(700), salt: digest_seed(800), value: 750 }
        };
        let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier, asset_id: asset, amount: part, destination_token_account: [9; 32], change_commitment: cc,
        };
        Stmt::Withdrawal(public, PoolV1PairForestWithdrawalWitnessV1 { input, change: chg })
    };
    Case { stmt, binding, spent: Vec::new(), snapshot }
}

fn label(out: &Out) -> String {
    match out {
        Ok(_) => "Ok".into(),
        Err(e) => {
            let s = format!("{e:?}");
            s.split(['{', ' ']).next().unwrap().to_string()
        }
    }
}

/// Run one case; assert the shipped and reference results are identical.
fn check(case: &Case, tally: &mut BTreeMap<String, usize>) -> bool {
    let (shipped, reference) = case.run();
    assert_eq!(shipped, reference, "shipped and reference compilations differ");
    *tally.entry(label(&shipped)).or_default() += 1;
    shipped.is_ok()
}

fn mutations() -> Vec<(&'static str, fn(&mut Case))> {
    vec![
        ("public anchor", |c| c.anchor()[0].0 ^= 1),
        ("public nullifier", |c| c.nullifier()[0].0 ^= 1),
        ("public change commitment", |c| c.change_commitment()[3].0 ^= 1),
        ("recipient commitment / amount", |c| match &mut c.stmt {
            Stmt::Transfer(p, _) => p.recipient_commitment[5].0 ^= 1,
            Stmt::Withdrawal(p, _) => p.amount += 1,
        }),
        ("recipient value / change value +1", |c| match &mut c.stmt {
            Stmt::Transfer(_, w) => w.recipient.value += 1,
            Stmt::Withdrawal(_, w) => w.change.value += 1,
        }),
        ("change value zero", |c| c.change().value = 0),
        ("input value zero", |c| c.input().pair.value = 0),
        ("nullifier already spent", |c| { let n = *c.nullifier(); c.spent.push(n) }),
        ("context pool", |c| c.binding.pool[0] ^= 1),
        ("context asset", |c| c.binding.asset_id.0 ^= 1),
        ("context anchor sequence", |c| c.binding.anchor_sequence += 1),
        ("public asset", |c| c.asset().0 ^= 1),
        ("snapshot pool", |c| c.snapshot.pool[3] ^= 1),
        ("snapshot sequence", |c| c.snapshot.sequence += 1),
        ("snapshot index and sequence", |c| { c.snapshot.sequence += 1; c.snapshot.next_pair_index += 1 }),
        ("snapshot current root", |c| c.snapshot.current_root[2].0 ^= 1),
        ("snapshot frontier 0", |c| c.snapshot.frontier[0][0].0 ^= 1),
        ("snapshot frontier non-canonical at lowest set bit", |c| {
            let n = c.snapshot.next_pair_index;
            let level = if n == 0 { 0 } else { n.trailing_zeros() as usize };
            c.snapshot.frontier[level][7].0 = P + 3;
        }),
        ("super-root sibling non-canonical", |c| c.input().super_root_siblings[1][3].0 = P),
        ("super-root sibling value", |c| c.input().super_root_siblings[0][0].0 ^= 1),
        ("super-root direction", |c| c.input().super_root_directions[2] ^= true),
        ("membership sibling non-canonical", |c| c.input().pair.membership.siblings[4][2].0 = P + 5),
        ("membership sibling value", |c| c.input().pair.membership.siblings[7][6].0 ^= 1),
        ("membership index bit", |c| c.input().pair.membership.index ^= 1 << 9),
        ("membership index out of range", |c| c.input().pair.membership.index = 1 << 20),
        ("input salt", |c| c.input().pair.salt[0].0 ^= 1),
        ("input nullifier key non-canonical", |c| c.input().pair.nullifier_key[0].0 = P),
        ("input selected side", |c| c.input().pair.selected_second ^= true),
        ("pair occupancy inverse", |c| c.input().pair.pair_leaf.second_occupancy_inverse.0 ^= 1),
        ("pair first commitment non-canonical", |c| c.input().pair.pair_leaf.first_commitment[0].0 = P),
        ("change owner key", |c| c.change().owner_key[0].0 ^= 1),
    ]
}

#[test]
fn shipped_compiler_equals_pre_migration_compiler() {
    let mut tally = BTreeMap::new();
    let mut base = Vec::new();
    for transfer in [true, false] {
        let case = honest(None, transfer);
        assert!(check(&case, &mut tally), "saved fixture must compile");
        base.push(case);
    }
    println!("saved fixtures: 2 compiled, shipped == reference");

    let mut rng = Rng(0x61_7573_7069_7331);
    let (mut ok, mut rejected, mut i) = (0u32, 0u32, 0u64);
    while ok < 512 {
        let case = honest(Some(&mut rng), i % 2 == 0);
        if check(&case, &mut tally) { ok += 1 } else { rejected += 1 }
        if base.len() < 2 + 64 {
            base.push(case);
        }
        i += 1;
    }
    println!("randomized: {ok} honest witnesses compiled (glue.rs generator and seed), {rejected} rejected identically, shipped == reference");

    let muts = mutations();
    let mut mutated = 0usize;
    for case in &base {
        for (_, m) in &muts {
            let mut c = case.clone();
            m(&mut c);
            check(&c, &mut tally);
            mutated += 1;
        }
    }
    println!("mutations: {} kinds x {} base cases = {mutated} cases, shipped == reference", muts.len(), base.len());
    println!("result tally (all cases): {tally:?}");
    assert!(tally.len() >= 10, "the mutations must reach many distinct error paths");
}

/// Teeth: the comparison distinguishes different compilations, and one
/// changed cell of the shipped semantic C1 is detected.
#[test]
fn comparison_has_teeth() {
    let case = honest(None, true);
    let (shipped, reference) = case.run();
    let mut shipped = shipped.unwrap();
    assert_eq!(shipped, reference.clone().unwrap());
    shipped.semantic_c1.c1[7][300].0 ^= 1;
    assert_ne!(Ok(shipped), reference);
    let mut other = case.clone();
    other.snapshot = snapshot_at([1; 32], [2; 32], 14);
    let (a, _) = other.run();
    assert_ne!(a.unwrap(), reference.unwrap());
    println!("comparison_has_teeth: a one-cell change and a different snapshot are detected");
}
