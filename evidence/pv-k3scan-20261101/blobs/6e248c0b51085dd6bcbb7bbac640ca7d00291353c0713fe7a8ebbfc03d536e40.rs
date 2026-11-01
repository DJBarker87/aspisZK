//! Owned record mapper for Charon/Aeneas; proof-only, no production dependency.
use super::*;

pub(super) fn records_reference_with_roots(input: PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<PoolV1OutputNoteWitnessV1>,
           chg: PoolV1OutputNoteWitnessV1, snapshot: PoolV1PairLiveSnapshotV1, asset: M31, empty: [Digest; 21]) -> (RW, RP) {
    let pair = input.pair;
    let mut bits = [0u32; 24];
    let mut sibs = [[0u32; 8]; 24];
    let mut level = 0;
    while level < 24 {
        bits[level] = if level == 0 { u32::from(pair.selected_second) }
            else if level <= 20 { (pair.membership.index >> ((level - 1) as u32)) & 1 }
            else { u32::from(input.super_root_directions[level - 21]) };
        let mut lane = 0;
        while lane < 8 {
            sibs[level][lane] = if level == 0 {
                if pair.selected_second { pair.pair_leaf.first_commitment[lane].0 }
                else { pair.pair_leaf.second_commitment[lane].0 }
            } else if level <= 20 { pair.membership.siblings[level-1][lane].0 }
            else { input.super_root_siblings[level-21][lane].0 };
            lane += 1;
        }
        level += 1;
    }
    let mut recipient_owner = ZERO8;
    let mut recipient_salt = ZERO8;
    let mut lane = 0;
    while lane < 8 {
        if let Some(r) = rec {
            recipient_owner[lane] = r.owner_key[lane].0;
            recipient_salt[lane] = r.salt[lane].0;
        }
        lane += 1;
    }
    let mut frontier = [[0u32; 8]; 20];
    let mut empty_raw = [[0u32; 8]; 20];
    let mut level = 0;
    while level < 20 {
        let mut lane = 0;
        while lane < 8 {
            frontier[level][lane] = snapshot.frontier[level][lane].0;
            empty_raw[level][lane] = empty[level][lane].0;
            lane += 1;
        }
        level += 1;
    }
    let w = RW {
        input_value: pair.value,
        output_value: out,
        change_value: chg.value,
        sk: raw_owned(pair.nullifier_key),
        salt: raw_owned(pair.salt),
        bits,
        sibs,
        pair_first: raw_owned(pair.pair_leaf.first_commitment),
        pair_occupied: pair.pair_leaf.second_occupied.0,
        pair_second: raw_owned(pair.pair_leaf.second_commitment),
        pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
        recipient_owner,
        recipient_salt,
        change_owner: raw_owned(chg.owner_key),
        change_salt: raw_owned(chg.salt),
    };
    let p = RP {
        transfer: rec.is_some(),
        asset: asset.0,
        next_pair_index: snapshot.next_pair_index,
        frontier,
        empty: empty_raw,
    };
    (w, p)
}


fn raw_owned(d: Digest) -> [u32; 8] {
    [d[0].0, d[1].0, d[2].0, d[3].0, d[4].0, d[5].0, d[6].0, d[7].0]
}

// Extraction adapter calls shipped records; it does not reimplement the mapper.
#[cfg(aeneas_ref)]
#[path = "pv_runjoin12_shipped.rs"]
pub(super) mod pv_runjoin12_shipped;
