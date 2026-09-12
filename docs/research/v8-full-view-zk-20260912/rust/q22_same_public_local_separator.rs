// Include this child module from `circle_candidate.rs` in an isolated pinned
// source copy. The eight coefficients use only fibres 4 and 6, so every q22
// schedule containing both fibres exposes the same column-zero functional.
#[cfg(test)]
mod v8_q22_same_public_local_separator {
    use super::CircleEncoder;
    use aspis_core::field::{M31, P};
    use aspis_statement::pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };

    const QUERIES: [usize; 2] = [4, 6];
    const LAMBDA: [u32; 8] = [
        1508290849, 1480589898, 639192798, 666893749,
        2147483646, 0, 1, 0,
    ];

    fn observed(encoder: &CircleEncoder, row: usize) -> M31 {
        let mut coordinate = 0usize;
        let mut value = M31::ZERO;
        for query in QUERIES {
            for slot in 0..4 {
                let coefficient = LAMBDA[coordinate];
                assert!(coefficient < P);
                value = value.add(M31(coefficient).mul(
                    encoder.encode_c1_basis_value(row, 4 * query + slot).unwrap(),
                ));
                coordinate += 1;
            }
        }
        value
    }

    #[test]
    fn fixed_pair_4_6_exposes_same_public_selection_row() {
        let encoder = CircleEncoder::new_for_domain_log(20);
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        let dependent = observed(&encoder, 1023);
        let mut surviving = 0usize;
        for cell in cells {
            if cell.column != 0 || cell.row == 1023 {
                continue;
            }
            let mut direction = observed(&encoder, cell.row as usize);
            if !active.contains(&cell.row) {
                direction = direction.sub(dependent);
            }
            assert_eq!(direction, M31::ZERO, "surviving column-zero mask row {}", cell.row);
            surviving += 1;
        }
        assert!(surviving > 0);
        assert_eq!(observed(&encoder, 913), M31(490597912));
    }
}
