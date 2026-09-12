// Include this file from `circle_candidate.rs` in an isolated source copy.
// It uses the actual private encoder and actual layout inventory. The sample
// is a falsification diagnostic, not a bad-schedule probability theorem.
#[cfg(test)]
mod v8_q22_row_1014_schedule_probe {
    use super::CircleEncoder;
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };

    fn observation(encoder: &CircleEncoder, row: usize, queries: &[usize; 22]) -> Vec<M31> {
        let mut out = Vec::with_capacity(88);
        for &query in queries {
            for slot in 0..4 {
                out.push(encoder.encode_c1_basis_value(row, 4 * query + slot).unwrap());
            }
        }
        out
    }

    fn insert(pivots: &mut [Option<Vec<M31>>], mut column: Vec<M31>) -> bool {
        for pivot in 0..column.len() {
            if column[pivot] == M31::ZERO {
                continue;
            }
            if let Some(base) = &pivots[pivot] {
                let scale = column[pivot];
                for i in pivot..column.len() {
                    column[i] = column[i].sub(scale.mul(base[i]));
                }
            } else {
                let inverse = column[pivot].inv();
                for value in &mut column[pivot..] {
                    *value = value.mul(inverse);
                }
                pivots[pivot] = Some(column);
                return true;
            }
        }
        false
    }

    fn hidden(encoder: &CircleEncoder, queries: &[usize; 22]) -> (usize, bool) {
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        let dependent = observation(encoder, 1023, queries);
        let mut pivots = vec![None; 88];
        for cell in cells {
            if cell.column != 3 || cell.row == 1023 || cell.row == 1014 {
                continue;
            }
            let mut direction = observation(encoder, cell.row as usize, queries);
            if !active.contains(&cell.row) {
                for (value, correction) in direction.iter_mut().zip(&dependent) {
                    *value = value.sub(*correction);
                }
            }
            insert(&mut pivots, direction);
        }
        let rank = pivots.iter().filter(|pivot| pivot.is_some()).count();
        let shift_independent = insert(&mut pivots, observation(encoder, 1014, queries));
        (rank, !shift_independent)
    }

    fn random_distinct(mut state: u64) -> [usize; 22] {
        let mut out = [0usize; 22];
        for i in 0..22 {
            loop {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                let candidate = (state as usize) & ((1usize << 18) - 1);
                if !out[..i].contains(&candidate) {
                    out[i] = candidate;
                    break;
                }
            }
        }
        out
    }

    #[test]
    fn diagnostic_row_1014_containment_across_schedules() {
        let encoder = CircleEncoder::new_for_domain_log(20);
        let mut hidden_count = 0usize;
        let mut total = 0usize;
        for start in [0usize, 1, 17, 1024, 65536] {
            let queries = core::array::from_fn(|index| start + index);
            let (rank, is_hidden) = hidden(&encoder, &queries);
            println!("Q22_CONTAINMENT kind=consecutive start={start} rank={rank} hidden={is_hidden}");
            hidden_count += usize::from(is_hidden);
            total += 1;
        }
        for seed in 1u64..=32 {
            let queries = random_distinct(seed.wrapping_mul(0x9e3779b97f4a7c15));
            let (rank, is_hidden) = hidden(&encoder, &queries);
            println!("Q22_CONTAINMENT kind=xorshift seed={seed} rank={rank} hidden={is_hidden}");
            hidden_count += usize::from(is_hidden);
            total += 1;
        }
        println!(
            "Q22_CONTAINMENT_SUMMARY total={total} hidden={hidden_count} exposed={}",
            total - hidden_count
        );
    }
}
