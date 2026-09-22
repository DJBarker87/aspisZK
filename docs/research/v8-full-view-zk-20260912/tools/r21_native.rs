//! R21 host-only native public-arithmetic relation.
//!
//! This is an arithmetic oracle for the ordinary and image terms only.  It is
//! deliberately not a verifier callback and does not include G or query
//! arithmetic.  The R16/R17/R19 sources are included by path without edits so
//! that this wrapper cannot silently acquire a production callback surface.

extern crate aspis_core as corelib;
extern crate aspis_statement;

use corelib::field::{qm31_sum_products4, M31, QM31};

pub type K = QM31;

#[path = "r16_basis_transport.rs"]
mod basis_transport;
#[path = "r17_weighted_groups.rs"]
mod r17_weighted_groups;
#[path = "r19_channel_ordinary.rs"]
mod r19_channel_ordinary;

/// Exact image term copied from `relation_callback.rs`.
#[inline]
fn image_terminal(t: K, b: K, c: K, a: [K; 4]) -> K {
    a[1]
        .mul(a[2])
        .mul(a[3])
        .mul(t.mul(a[0]).add(t.square().mul(b.mul(a[0].square()).sub(
            c.mul(a[0].square().mul(a[0])),
        ))))
        .mul_m31(M31(8_388_608))
}

#[cfg(not(target_os = "solana"))]
fn encoded_fields(fields: &[K]) -> Vec<u8> {
    let mut bytes = vec![0u8; fields.len() * 16];
    for (i, field) in fields.iter().enumerate() {
        field.write_le_bytes(&mut bytes[i * 16..(i + 1) * 16]);
    }
    bytes
}

/// Evaluate the R21 public arithmetic relation over its fixed 24-input ABI.
///
/// Inputs are `[audit[0..11], abc[0..3], alpha[0..4], beta, finals[0..4],
/// tau]`.  The ordinary terminal uses the actual R19 channel implementation,
/// actual R17 grouped kernel, and one 1024-entry heap workspace.  The image
/// term is retained separately, as in the source callback, while G/query
/// terms remain outside this oracle.
#[inline(never)]
pub fn compute(inputs: &[K; 24]) -> K {
    let audit: [K; 11] = core::array::from_fn(|i| inputs[i]);
    let abc: [K; 3] = core::array::from_fn(|i| inputs[11 + i]);
    let alpha: [K; 4] = core::array::from_fn(|i| inputs[14 + i]);
    let beta = inputs[18];
    let finals: [K; 4] = core::array::from_fn(|i| inputs[19 + i]);
    let tau = inputs[23];

    let kernel = r17_weighted_groups::Kernel::new(abc, alpha);
    let mut workspace = vec![K::ZERO; 1024];
    let ordinary = r19_channel_ordinary::terminal_shared(
        &audit,
        abc,
        alpha,
        beta,
        &mut workspace,
        &kernel,
    );

    // Host-only capture is intentionally immediately after ordinary
    // computation and is absent from SBF builds.
    #[cfg(not(target_os = "solana"))]
    if std::env::var_os("ASPIS_R21_CAPTURE_PUBLIC").is_some() {
        eprintln!("R21_PUBLIC_INPUTS {{\"fields\":{:?}}}", encoded_fields(inputs));
    }

    let ordinary_dot = qm31_sum_products4(ordinary, finals);
    let image_scale = K::ONE.sub(beta).add(beta.mul(tau.square()));
    let image = image_scale
        .mul(image_terminal(tau, abc[1], abc[2], alpha))
        .mul(finals[3]);
    ordinary_dot.add(image)
}
