//! FIRST ATTEMPT / NOT COMPILED. Include this CHILD MODULE only inside an
//! isolated copy of crates/aspis-prover/src/circle_candidate.rs so the existing
//! crate-private scalar encoder is accessible. Do not alter the encoder.
//!
//! Confirms ONE exact dual certificate for artificial trace offsets at a
//! predeclared q22 schedule. It is NOT a valid-witness privacy attack.
#[cfg(test)]
mod v8_privacy_raw_opening_certificate {
    use super::CircleEncoder;
    use aspis_core::field::{M31, P};
    use aspis_statement::pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };
    const LAMBDA: [u32;88] = [
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        1508290849,1480589898,639192798,666893749,0,0,0,0,
        2147483646,0,1,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,
    ];
    fn observed(encoder: &CircleEncoder, row: usize) -> M31 {
        LAMBDA.iter().enumerate().fold(M31::ZERO, |a,(i,&c)| {
            assert!(c < P);
            // q_i = i for 0 <= i < 22; four literal source fiber slots each.
            a.add(M31(c).mul(encoder.encode_c1_basis_value(row,i).unwrap()))
        })
    }
    #[test]
    fn repaired_mask_map_has_this_annihilator() {
        let encoder=CircleEncoder::new_for_domain_log(20);
        let active=pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        let dependent=observed(&encoder,1023);
        let mut surviving=0;
        for cell in cells {
            if cell.column!=3 || cell.row==1023 || cell.row==1014 {continue;}
            let mut got=observed(&encoder,cell.row as usize);
            if !active.contains(&cell.row){got=got.sub(dependent);}
            assert_eq!(got,M31::ZERO,"surviving mask row {}",cell.row);
            surviving+=1;
        }
        assert_eq!(surviving,222);
        let removed=observed(&encoder,1014);
        assert_eq!(removed,M31(170822063));
        assert_ne!(removed,M31::ZERO);
        // Independent actual full encoder, not merely the scalar path.
        let mut unit=vec![M31::ZERO;1024];unit[1014]=M31::ONE;
        let encoded=encoder.encode_c1_message(&unit).unwrap();
        let direct=LAMBDA.iter().enumerate().fold(M31::ZERO,|a,(i,&c)|a.add(M31(c).mul(encoded[i])));
        assert_eq!(direct,removed);
        println!("certificate checked against actual encoder; valid-witness pair NOT constructed; global ZK NOT proved");
    }
}
