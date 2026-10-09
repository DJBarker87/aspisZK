#![cfg(feature = "r0")]
use aspis_core::field::{WideExact, P, QM31};
use aspis_core::state_only_prefix::r0::*;
use aspis_core::state_only_sumcheck::r0 as sumcheck;
use sha2::{Digest, Sha256};
use std::cell::RefCell;
const PROOF: &[u8] = include_bytes!("../../../results/r0-samplers-20261009/semantic-kat.bin");
const PUBLIC: &[u8] =
    include_bytes!("../../../results/r0-samplers-20261009/semantic-kat-public.bin");
const STATES: &[u8] =
    include_bytes!("../../../results/r0-samplers-20261009/semantic-kat-states.bin");
const CHALLENGES: &[u8] =
    include_bytes!("../../../results/r0-samplers-20261009/semantic-kat-challenges.bin");
thread_local! { static READS: RefCell<Vec<Vec<u8>>> = const { RefCell::new(Vec::new()) }; }
fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let input: Vec<u8> = parts.concat();
    READS.with(|r| r.borrow_mut().push(input.clone()));
    Sha256::digest(input).into()
}
fn transcript() -> SemanticTranscript {
    SemanticTranscript::new(hash, PUBLIC, PROOF[..32].try_into().unwrap()).unwrap()
}

#[test]
fn independent_fixed_trace_kat_every_row_and_hash_read() {
    READS.with(|r| r.borrow_mut().clear());
    let prefix = Prefix::parse(PROOF).unwrap();
    let mut t = transcript();
    for row in 0..27u8 {
        let before = t.state();
        if row < 25 {
            let challenge = t.semantic(row, prefix.record(row).unwrap()).unwrap();
            let mut encoded = [0; 16];
            challenge.write_le_bytes(&mut encoded);
            assert_eq!(
                encoded,
                CHALLENGES[row as usize * 16..][..16],
                "challenge row {row}"
            );
        } else {
            let z = t
                .challenge_reference_circle_point(row, prefix.record(row).unwrap())
                .unwrap();
            let mut encoded = [0; 32];
            z.x.write_le_bytes(&mut encoded[..16]);
            z.y.write_le_bytes(&mut encoded[16..]);
            assert_eq!(encoded, CHALLENGES[400 + (row as usize - 25) * 32..][..32]);
        }
        assert_eq!(
            t.state(),
            STATES[row as usize * 32..][..32],
            "state row {row}"
        );
        READS.with(|r| {
            let r = r.borrow();
            let start = 1 + row as usize * 3;
            assert_eq!(r.len(), start + 3);
            assert_eq!(
                r[start],
                [&before[..], &[0, 0xa0 + row], prefix.record(row).unwrap()].concat()
            );
            assert_eq!(&r[start + 1][..32], &r[start + 2][..32]);
            assert_eq!(r[start + 1][32], 1);
            assert_eq!(r[start + 2][32], 2);
        });
    }
    assert_eq!(t.next_row(), 27);
    let mut t = transcript();
    let semantic = begin(&prefix, &mut t).unwrap();
    let checked = sumcheck::verify(&prefix, &mut t).unwrap();
    for (row, value) in semantic.with_alphas(&checked.alpha).iter().enumerate() {
        assert_eq!(&value.to_le_bytes()[..16], &CHALLENGES[row * 16..][..16]);
        assert_eq!(value.c1(), QM31::ZERO);
    }
    assert_eq!(checked.terminal_claim, prefix.point_claims().unwrap()[0][0]);
    assert_ne!(prefix.point_claims().unwrap()[0][28], WideExact::ZERO);
}

#[test]
fn parser_and_row_order_teeth_for_every_row() {
    let prefix = Prefix::parse(PROOF).unwrap();
    let mut t = transcript();
    for row in 0..27u8 {
        let good = prefix.record(row).unwrap();
        for mode in 0..4 {
            let mut bad = good.to_vec();
            match mode {
                0 => bad[0] ^= 0xff,
                1 => bad[1] ^= 1,
                2 => {
                    bad.pop();
                }
                _ => bad.push(0),
            }
            assert!(parse_record(row, &bad).is_err(), "row {row} mode {mode}");
            let state = t.state();
            let result = if row < 25 {
                t.semantic(row, &bad).map(|_| ())
            } else {
                t.challenge_reference_circle_point(row, &bad).map(|_| ())
            };
            assert!(result.is_err());
            assert_eq!(t.state(), state);
            assert_eq!(t.next_row(), row);
        }
        if row >= 14 {
            let count = row_shape(row).unwrap().1 / 32;
            // All eight limbs, and the last array element (including D).
            for value in [0, count - 1] {
                for limb in 0..8 {
                    let mut bad = good.to_vec();
                    let offset = 5 + value * 32 + limb * 4;
                    bad[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
                    assert_eq!(
                        parse_record(row, &bad),
                        Err(Error::NonCanonical { row, value })
                    );
                }
            }
        }
        assert!(t.semantic(row + 1, good).is_err());
        if row < 25 {
            t.semantic(row, good).unwrap();
        } else {
            t.challenge_reference_circle_point(row, good).unwrap();
        }
        assert!(if row < 25 {
            t.semantic(row, good).map(|_| ())
        } else {
            t.challenge_reference_circle_point(row, good).map(|_| ())
        }
        .is_err());
    }
    let mut extra = PROOF.to_vec();
    extra.push(0);
    assert!(matches!(Prefix::parse(&extra), Err(Error::TrailingBytes)));
    for len in 0..PROOF.len() {
        assert!(Prefix::parse(&PROOF[..len]).is_err());
    }
}

#[test]
fn every_sumcheck_boundary_has_teeth_and_full_e_values_survive() {
    let prefix = Prefix::parse(PROOF).unwrap();
    let mut offset = 32;
    for row in 0..27u8 {
        if (15..=24).contains(&row) {
            let mut bad = PROOF.to_vec();
            // c0's v limb: canonical but changes the boundary in E.
            bad[offset + 5 + 16..offset + 5 + 20].copy_from_slice(&1u32.to_le_bytes());
            let parsed = Prefix::parse(&bad).unwrap();
            let mut t = transcript();
            begin(&parsed, &mut t).unwrap();
            assert_eq!(
                sumcheck::verify(&parsed, &mut t),
                Err(Error::Boundary {
                    round: row as usize - 15
                })
            );
        }
        offset += prefix.record(row).unwrap().len();
    }
    let mut poly = [WideExact::ZERO; 28];
    poly[27] = WideExact::V;
    assert_eq!(sumcheck::boundary(&poly), WideExact::V);
    assert_eq!(sumcheck::evaluate(&poly, QM31::ONE), WideExact::V);
}

#[test]
fn eta_zero_and_reference_circle_fallbacks_do_not_retry() {
    fn zero(_: &[&[u8]]) -> [u8; 32] {
        [0; 32]
    }
    let prefix = Prefix::parse(PROOF).unwrap();
    let mut t = SemanticTranscript::new(zero, PUBLIC, prefix.c1_root).unwrap();
    let c = begin(&prefix, &mut t).unwrap();
    assert_eq!(c.eta, QM31::ZERO);
    for row in 15..=24 {
        assert_eq!(
            t.semantic(row, prefix.record(row).unwrap()).unwrap(),
            QM31::ZERO
        );
    }
    let z0 = t
        .challenge_reference_circle_point(25, prefix.record(25).unwrap())
        .unwrap();
    let z1 = t
        .challenge_reference_circle_point(26, prefix.record(26).unwrap())
        .unwrap();
    assert_ne!(z0, z1);
    assert_eq!(t.next_row(), 27);
}
