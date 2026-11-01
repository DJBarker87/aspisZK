//! Safe control reference for op259. Included only by cfg(kani) proof crates.
use aspis_core::{circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint},
                 r0_transcript::CircleRow, transcript::circle_fallback_point};

pub fn circle_sample(block: &[u8; 32], row: CircleRow) -> SecureCirclePoint {
    let parameter = aspis_r1_cost_probe::sampler::qm31_sample(block);
    match secure_ood_circle_point_from_parameter(parameter) {
        Ok(point) => point,
        Err(_) => match row {
            CircleRow::First => circle_fallback_point(0),
            CircleRow::Second => circle_fallback_point(1),
        },
    }
}
