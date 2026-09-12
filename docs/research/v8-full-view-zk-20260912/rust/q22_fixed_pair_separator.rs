// Include this child module from `circle_candidate.rs` in an isolated pinned
// source copy. It certifies an eight-coordinate separator supported only on
// q22 fibres 1 and 2. Therefore every full q22 schedule containing both
// fibres inherits the separator, regardless of its other twenty queries.
#[cfg(test)]
mod v8_q22_fixed_pair_separator {
    use super::CircleEncoder;
    use aspis_core::field::{M31, P};
    use aspis_statement::pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };

    const QUERIES: [usize; 2] = [1, 2];
    const LAMBDA: [u32; 8] = [
        1716687237, 1731393124, 430796410, 416090523,
        1986164149, 0, 161319498, 0,
    ];

    fn observed(encoder: &CircleEncoder, row: usize) -> M31 {
        let mut coordinate = 0usize;
        let mut value = M31::ZERO;
        for query in QUERIES {
            for slot in 0..4 {
                let coefficient = LAMBDA[coordinate];
                assert!(coefficient < P);
                value = value.add(
                    M31(coefficient).mul(
                        encoder.encode_c1_basis_value(row, 4 * query + slot).unwrap(),
                    ),
                );
                coordinate += 1;
            }
        }
        value
    }

    #[test]
    fn fixed_pair_1_2_exposes_removed_row_1014() {
        let encoder = CircleEncoder::new_for_domain_log(20);
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        let dependent = observed(&encoder, 1023);
        let mut surviving = 0usize;
        for cell in cells {
            if cell.column != 3 || cell.row == 1023 || cell.row == 1014 {
                continue;
            }
            let mut direction = observed(&encoder, cell.row as usize);
            if !active.contains(&cell.row) {
                direction = direction.sub(dependent);
            }
            assert_eq!(direction, M31::ZERO, "surviving mask row {}", cell.row);
            surviving += 1;
        }
        assert_eq!(surviving, 222);
        assert_eq!(observed(&encoder, 1014), M31::ONE);
    }
}
