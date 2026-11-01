use aspis_core::{circle::{secure_ood_circle_point_from_parameter,SecureCirclePoint},
    r0_transcript::CircleRow,transcript::circle_fallback_point};
// The host path below resolves the byte-pinned shipped source, without editing it.
#[path = "../../codex-pv-cblib-20261027/source/crates/aspis-r1-cost-probe/src/sampler.rs"]
pub mod shipped_sampler;
// Closure-free owned safe reference. All arithmetic is the same shipped call.
pub fn circle_reference(block: &[u8;32], row: CircleRow) -> SecureCirclePoint {
    let parameter=shipped_sampler::qm31_sample(block);
    match secure_ood_circle_point_from_parameter(parameter) {
        Ok(point) => point,
        Err(_) => match row {
            CircleRow::First => circle_fallback_point(0),
            CircleRow::Second => circle_fallback_point(1),
        }
    }
}

#[cfg(test)]
mod checks {
    use super::*;
    #[test]
    fn native_reference_matches() {
        let mut checked=0;let mut fallback=0;let mut accepted=0;
        let mut check=|block:[u8;32]| {
            for row in [CircleRow::First,CircleRow::Second] {
                let parameter=shipped_sampler::qm31_sample(&block);
                match secure_ood_circle_point_from_parameter(parameter) {
                    Ok(_)=>accepted+=1,Err(_)=>fallback+=1,
                }
                assert_eq!(shipped_sampler::circle_sample(&block,row),circle_reference(&block,row));
                checked+=1;
            }
        };
        check([0;32]);check([255;32]);
        for bit in 0..256 {let mut x=[0;32];x[bit/8]=1<<(bit%8);check(x);}
        let mut seed=0x123456789abcdef0u64;
        for _ in 0..4096 {
            let mut b=[0u8;32];
            for byte in &mut b {seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);*byte=(seed>>32)as u8;}
            check(b);
        }
        assert!(fallback>0 && accepted>0);
        println!("native/reference checks={checked}, accepted={accepted}, fallback={fallback}");
    }
}
