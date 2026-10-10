//! Native C5 preflight: record field components using the unchanged C3 prover inputs.
use anyhow::{anyhow, ensure, Result};
use aspis_core::field::{WideExact as E, CM31, M31, QM31};
use std::{fs, path::PathBuf};
fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    let name = &args[1];
    let previous = PathBuf::from(&args[2]);
    let out = PathBuf::from(&args[3]);
    ensure!(!out.exists(), "do not overwrite preflight evidence");
    let f = aspis_prover::r0_fixture::prepare(name == "withdrawal");
    let proof = {
        let masks = core::array::from_fn(|lane| {
            (0..1024)
                .map(|r| M31(((lane + 16) * 103 + r * 7 + 19) as u32))
                .collect()
        });
        let d = core::array::from_fn(|row| QM31 {
            c0: CM31::new(M31(row as u32 + 3), M31(11)),
            c1: CM31::new(M31(17), M31(19)),
        });
        let g = core::array::from_fn(|row| QM31::from_cm31(CM31::from_m31(M31(row as u32 + 5))));
        aspis_prover::r0_probe::r0_prove(
            f.public(),
            &f.compiled,
            &masks,
            &d,
            &g,
            aspis_prover::HOST_HASH,
        )
    }
    .map_err(|e| anyhow!("prove: {e:?}"))?;

    let expected = fs::read(previous.join(format!("{name}.proof.bin")))?;
    ensure!(
        proof == expected,
        "passive preflight changed C3 proof bytes"
    );
    let r = aspis_core::r0_probe::narrow_preflight::take();
    let q = r.first_q.map(|v| E::from_limbs(v).unwrap());
    let a = E::from_limbs(r.alpha_k).unwrap();
    let value = q[0].add(a.mul(q[1].add(a.mul(q[2].add(a.mul(q[3]))))));
    ensure!(
        value.to_limbs() == r.first_value,
        "independent first-fold witness differs"
    );
    let record = serde_json::json!({"configuration":"C5(b) preflight","variant":name,
        "source_revision":std::env::var("ASPIS_SOURCE_REVISION")?,
        "retained_c3_proof_bytes_equal":true,"same_row30_block":true,
        "gamma":r.gamma,"alpha_e":r.alpha_e,"alpha_k":r.alpha_k,
        "quotient_coefficients_with_nonzero_high_k":r.high_q,
        "wide_alpha_fold_coefficients_with_nonzero_high_k":r.high_f_e,
        "k_alpha_fold_coefficients_with_nonzero_high_k":r.high_f_k,
        "first_index":r.first_index,"first_fold_coefficient":r.first_value,"first_four_quotient_coefficients":r.first_q,
        "independent_horner_recheck":true,"can_encode_unchanged_fold_in_k":r.high_f_k==0,
        "cu_measurement":false});
    fs::write(out, serde_json::to_vec_pretty(&record)?)?;
    println!("{record}");
    Ok(())
}
