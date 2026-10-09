extern crate std;
use super::{
    basis::{BasisSize, NaturalBasis},
    chord,
    domain::{self, FibreIndex, InitialIndex, Point},
    encoder, fold, merkle,
    opening::{self, OpeningData},
    prover::{self, Commitment, CommitmentTime, EncodingDomain},
    transcript::{OpeningTranscript, SemanticBoundary, SemanticMessage, SemanticTranscript},
    verifier,
    wire::{OpeningProof, PROOF_BYTES},
    Error, Message,
};
use crate::{
    field::{WideExact as E, P},
    r0_transcript,
};
use sha2::{Digest, Sha256};
use std::{format, println, time::Instant, vec::Vec};
fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}
fn value(seed: u32, index: usize) -> E {
    E::from_limbs(core::array::from_fn(|h| {
        (seed + (index as u32 + 1) * (h as u32 + 3) + 17 * (h * h) as u32) % P
    }))
    .unwrap()
}
fn fields<const N: usize>(seed: u32) -> [E; N] {
    core::array::from_fn(|i| value(seed, i))
}
fn hex(x: &[u8]) -> std::string::String {
    x.iter().map(|b| format!("{b:02x}")).collect()
}
fn decode_hex(s: &str) -> [u8; 32] {
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}
fn fixture() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../results/r0-opening-20261009/kats.json"
    )))
    .unwrap()
}
fn json_e(v: &serde_json::Value) -> E {
    E::from_limbs(core::array::from_fn(|i| v[i].as_u64().unwrap() as u32)).unwrap()
}
fn public() -> Vec<u8> {
    std::vec![0;1+32+32+4+1+32+1+8+640+32+640]
}
fn semantic(hashfn: crate::HashFn, roots: [[u8; 32]; 2]) -> SemanticTranscript {
    let mut t = SemanticTranscript::new(hashfn, &public(), roots[0]).unwrap();
    for row in 0..25 {
        let h = fields::<28>(row);
        let m = match row {
            2 => SemanticMessage::C2Root(roots[1]),
            14 => SemanticMessage::MaskSum(value(14, 0)),
            15..=24 => SemanticMessage::RoundPolynomial(&h),
            _ => SemanticMessage::None,
        };
        t.sample(m).unwrap();
    }
    t
}
#[test]
fn data_bit_order_masks_and_claims() {
    let indicator = opening::indicator();
    assert_eq!(indicator.iter().filter(|&&x| x == E::ONE).count(), 810);
    assert_eq!(
        opening::COPY_ACTIVE_ROW_MASKS
            .iter()
            .map(|x| x.count_ones())
            .sum::<u32>(),
        214
    );
    assert_eq!(opening::inactive(1024), Err(Error::IndexOutOfRange));
    for r in 0..1024 {
        let a = core::array::from_fn(|j| {
            if (r >> (9 - j)) & 1 == 0 {
                E::ZERO
            } else {
                E::ONE
            }
        });
        let ps = opening::points_from_alphas(&a);
        for (p, n) in ps.iter().zip([r, (r + 1) % 1024, r ^ 12]) {
            for (b, &x) in p.iter().enumerate() {
                assert_eq!(x, if (n >> b) & 1 == 0 { E::ZERO } else { E::ONE });
            }
        }
    }
    let p = fields::<10>(57);
    let w = opening::eq_weight(&p);
    assert_eq!(w.iter().fold(E::ZERO, |a, &b| a.add(b)), E::ONE);
    let messages: Vec<_> = (0..29).map(|l| fields::<1024>(l)).collect();
    let points = opening::points_from_alphas(&p);
    let claims = prover::honest_claims(&messages, &points).unwrap();
    let z = [
        r0_transcript::circle_sample(&[7; 32], r0_transcript::CircleRow::First),
        r0_transcript::circle_sample(&[11; 32], r0_transcript::CircleRow::Second),
    ]
    .map(|z| Point {
        x: E::from_qm31(z.x),
        y: E::from_qm31(z.y),
    });
    let data = OpeningData {
        roots: [[0; 32]; 2],
        z,
        y: [[E::ZERO; 2]; 29],
        points,
        claims,
    };
    let gamma = value(59, 0);
    let kappa = value(61, 0);
    let g = opening::powers::<29>(gamma);
    let batch =
        core::array::from_fn(|r| (0..29).fold(E::ZERO, |s, l| s.add(g[l].mul(messages[l][r]))));
    let v = prover::v_honest(&messages, gamma).unwrap();
    assert_eq!(
        data.claim(gamma, v, kappa),
        opening::dot(&batch, &data.weights(kappa))
    );
}
#[test]
fn quotient_sparse_system_and_round_table() {
    let basis = NaturalBasis::new(BasisSize::Initial).unwrap();
    let t = fields::<1024>(917);
    let c0 = r0_transcript::circle_sample(&[17; 32], r0_transcript::CircleRow::First);
    let c1 = r0_transcript::circle_sample(&[29; 32], r0_transcript::CircleRow::Second);
    let a = Point {
        x: E::from_qm31(c0.x),
        y: E::from_qm31(c0.y),
    };
    for b in [
        Point {
            x: E::from_qm31(c1.x),
            y: E::from_qm31(c1.y),
        },
        Point {
            x: a.x,
            y: a.y.neg(),
        },
    ] {
        let z = [a, b];
        let y = z.map(|z| encoder::eval_message(&t, z));
        let q = prover::quotient(&basis, z, &t, y).unwrap();
        let i = chord::interpolant(a, b, y).unwrap();
        let line = chord::Secant::from_points(a, b);
        assert_eq!(
            chord::chord_message(&basis, line, &q).unwrap(),
            core::array::from_fn(|r| t[r].sub(i[r]))
        );
        assert_eq!(chord::e1(&basis, &q).unwrap(), E::ZERO);
        assert_eq!(chord::e2(&basis, line.b, line.c, &q).unwrap(), E::ZERO);
        for idx in [0, 1, 2, 3, 713, 1048575] {
            let idx = InitialIndex::new(idx).unwrap();
            assert_eq!(
                encoder::exact_initial_encoder(&q, idx).mul(line.line_word(idx)),
                encoder::exact_initial_encoder(&t, idx)
                    .sub(encoder::exact_initial_encoder(&i, idx))
            );
        }
        assert_eq!(
            prover::quotient(&basis, z, &t, [y[0].add(E::ONE), y[1]]),
            Err(Error::QuotientNotInImage)
        );
        let w = fields::<1024>(313);
        let c = prover::round_polynomial(&q, &w);
        assert_eq!(
            c[0].add(c[4]),
            fold::quarter::<E>().mul(opening::dot(&q, &w))
        );
        for alpha in [E::ZERO, E::ONE, value(811, 0)] {
            let eval = c.iter().rev().fold(E::ZERO, |s, &x| s.mul(alpha).add(x));
            assert_eq!(
                eval,
                fold::quarter::<E>().mul(opening::dot(
                    &fold::fold_message(alpha, &q),
                    &fold::dual_fold(alpha, &w)
                ))
            );
        }
    }
}
#[test]
fn p1_whole_transcript_and_merkle_kat() {
    let kat = fixture();
    let rows = &kat["rows"];
    let roots = [
        core::array::from_fn(|i| i as u8),
        core::array::from_fn(|i| 31 - i as u8),
    ];
    let mut t = SemanticTranscript::new(hash, &public(), roots[0]).unwrap();
    for row in 0..25 {
        let h = fields::<28>(row as u32);
        let m = match row {
            2 => SemanticMessage::C2Root(roots[1]),
            14 => SemanticMessage::MaskSum(value(14, 0)),
            15..=24 => SemanticMessage::RoundPolynomial(&h),
            _ => SemanticMessage::None,
        };
        let challenge = t.sample(m).unwrap();
        assert_eq!(challenge, json_e(&rows[row]["result"]));
        assert_eq!(hex(&t.state()), rows[row]["state"].as_str().unwrap());
    }
    let flat = fields::<87>(101);
    let claims = core::array::from_fn(|j| core::array::from_fn(|l| flat[29 * j + l]));
    let boundary = t.finish(claims, true).unwrap();
    let mut t = OpeningTranscript::new(hash, &boundary);
    let z0 = t.z0(&claims).unwrap();
    assert_eq!(hex(&t.state()), rows[25]["state"].as_str().unwrap());
    let y0 = fields::<29>(211);
    let z1 = t.z1(&y0).unwrap();
    assert_eq!(hex(&t.state()), rows[26]["state"].as_str().unwrap());
    for (j, z) in [z0, z1].iter().enumerate() {
        assert_eq!(z.x, json_e(&rows[25 + j]["result"][0]));
        assert_eq!(z.y, json_e(&rows[25 + j]["result"][1]));
    }
    let flat = fields::<58>(307);
    let y = core::array::from_fn(|l| [flat[2 * l], flat[2 * l + 1]]);
    let gamma = t.gamma(&y).unwrap();
    assert_eq!(gamma, json_e(&rows[27]["result"]));
    assert_eq!(hex(&t.state()), rows[27]["state"].as_str().unwrap());
    let v = value(401, 0);
    let kappa = t.kappa(v).unwrap();
    assert_eq!(kappa, json_e(&rows[28]["result"]));
    assert_eq!(hex(&t.state()), rows[28]["state"].as_str().unwrap());
    let tau = t.tau().unwrap();
    assert_eq!(tau, json_e(&rows[29]["result"]));
    assert_eq!(hex(&t.state()), rows[29]["state"].as_str().unwrap());
    let data = OpeningData {
        roots,
        z: [z0, z1],
        y,
        points: boundary.points(),
        claims,
    };
    for j in 0..3 {
        for b in 0..10 {
            assert_eq!(data.points[j][b], json_e(&kat["points"][j][b]));
        }
    }
    let w = data.weights(kappa);
    let wbytes: Vec<_> = w.iter().flat_map(|x| x.to_le_bytes()).collect();
    assert_eq!(
        hex(&hash(&[&wbytes])),
        kat["weights_sha256"].as_str().unwrap()
    );
    let cp = data.claim_prime(gamma, v, kappa).unwrap();
    assert_eq!(cp, json_e(&kat["claim_prime"]));
    let sent = fields::<6>(503);
    let c = [
        sent[0],
        sent[1],
        sent[2],
        sent[3],
        fold::quarter::<E>().mul(cp).sub(sent[0]),
        sent[4],
        sent[5],
    ];
    for j in 0..7 {
        assert_eq!(c[j], json_e(&kat["polynomial"][j]));
    }
    let alpha = t.alpha(&c).unwrap();
    assert_eq!(alpha, json_e(&rows[30]["result"]));
    assert_eq!(hex(&t.state()), rows[30]["state"].as_str().unwrap());
    let s = t.queries(&fields::<256>(601)).unwrap();
    assert_eq!(hex(&t.state()), rows[31]["state"].as_str().unwrap());
    for j in 0..22 {
        assert_eq!(
            s.ordered()[j],
            rows[31]["result"][j].as_u64().unwrap() as u32
        );
    }
    assert_eq!(t.tau(), Err(Error::Schedule));
    let path = core::array::from_fn(|d| {
        core::array::from_fn(|s| decode_hex(kat["merkle"]["siblings"][d][s].as_str().unwrap()))
    });
    let root = decode_hex(kat["merkle"]["root"].as_str().unwrap());
    let leaf = merkle::leaf(hash, merkle::C1_TAG, &[0; 480]);
    assert!(merkle::verify_pair(
        hash,
        &[root, root],
        FibreIndex::new(12345).unwrap(),
        [leaf, leaf],
        &[path, path]
    ));
    assert!(!merkle::verify_pair(
        hash,
        &[root, root],
        FibreIndex::new(12344).unwrap(),
        [leaf, leaf],
        &[path, path]
    ));
}
#[test]
fn parser_sampler_and_schedule_rejections() {
    let proof = OpeningProof {
        y0: [E::ZERO; 29],
        y: [[E::ZERO; 2]; 29],
        v: E::ZERO,
        coefficients: [E::ZERO; 6],
        final_message: [E::ZERO; 256],
        openings: std::vec![super::wire::FibreOpening::empty();22],
    };
    let bytes = proof.encode().unwrap();
    assert_eq!(bytes.len(), PROOF_BYTES);
    assert_eq!(OpeningProof::parse(&bytes).unwrap(), proof);
    for n in [0, 1, 4, 5, 932, PROOF_BYTES - 1] {
        assert_eq!(OpeningProof::parse(&bytes[..n]), Err(Error::Parse));
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert_eq!(OpeningProof::parse(&extra), Err(Error::Parse));
    // Every field limb in every record, including all narrow lane openings.
    let starts = [
        (5, 29 * 32),
        (5 + 29 * 32 + 5, 58 * 32),
        (10 + (29 + 58) * 32 + 5, 32),
        (15 + (29 + 58 + 1) * 32 + 5, 6 * 32),
        (20 + (29 + 58 + 1 + 6) * 32 + 5, 256 * 32),
    ];
    for (start, len) in starts {
        for offset in (start..start + len).step_by(4) {
            let mut bad = bytes.clone();
            bad[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(OpeningProof::parse(&bad), Err(Error::NonCanonical));
        }
    }
    let start = 30 + (29 + 58 + 1 + 6 + 256) * 32;
    for u in 0..22 {
        for offset in (start + u * super::wire::FIBRE_BYTES
            ..start + u * super::wire::FIBRE_BYTES + super::wire::FIBRE_VALUE_BYTES)
            .step_by(4)
        {
            let mut bad = bytes.clone();
            bad[offset..offset + 4].copy_from_slice(&P.to_le_bytes());
            assert_eq!(OpeningProof::parse(&bad), Err(Error::NonCanonical));
        }
    }
    for offset in [0, 1, 933, 934] {
        let mut bad = bytes.clone();
        bad[offset] ^= 1;
        assert_eq!(OpeningProof::parse(&bad), Err(Error::Parse));
    }
    let mut wrong = proof.clone();
    wrong.openings[0].values[0][0] = E::V;
    assert_eq!(wrong.encode(), Err(Error::WrongField));
    let mut st = SemanticTranscript::new(hash, &public(), [0; 32]).unwrap();
    let state = st.state();
    assert_eq!(
        st.sample(SemanticMessage::MaskSum(E::ZERO)),
        Err(Error::Schedule)
    );
    assert_eq!(st.state(), state);
    assert!(matches!(
        st.finish([[E::ZERO; 29]; 3], true),
        Err(Error::Schedule)
    ));
    assert!(matches!(
        semantic(hash, [[0; 32]; 2]).finish([[E::ZERO; 29]; 3], false),
        Err(Error::Semantic)
    ));
    // Hash oracle with repeated words forces sampler exhaustion; no fallback S.
    fn repeated(_: &[&[u8]]) -> [u8; 32] {
        [0; 32]
    }
    let boundary = semantic(repeated, [[0; 32]; 2])
        .finish([[E::ZERO; 29]; 3], true)
        .unwrap();
    assert!(matches!(
        verifier::prepare(repeated, &boundary, &proof),
        Err(Error::Sampler)
    ));
    // Draw 24 succeeds exactly at block end: state of block 4 is returned.
    let mut blocks = [[0; 32]; 8];
    let states = core::array::from_fn(|k| [k as u8; 32]);
    for draw in 0..24 {
        let word = if draw < 21 {
            draw
        } else if draw == 23 {
            21
        } else {
            0
        } as u32;
        blocks[draw / 8][(draw % 8) * 4..(draw % 8 + 1) * 4].copy_from_slice(&word.to_le_bytes());
    }
    assert_eq!(
        r0_transcript::queries_from_pairs(&blocks, &states)
            .unwrap()
            .1,
        states[3]
    );
}

fn honest_messages() -> Vec<Message<E>> {
    (0..29)
        .map(|l| {
            core::array::from_fn(|r| {
                E::from_limbs(core::array::from_fn(|h| {
                    if h < (if l < 26 { 1 } else { 4 }) {
                        (((l + 3) * (r + 7) * (h + 1) + r * r + 19 * h + 11) % P as usize) as u32
                    } else {
                        0
                    }
                }))
                .unwrap()
            })
        })
        .collect()
}
fn reopen(proof: &mut OpeningProof, boundary: &SemanticBoundary, c1: &Commitment, c2: &Commitment) {
    let p = verifier::prepare(hash, boundary, proof).unwrap();
    for (u, opening) in p
        .challenges
        .queries
        .sorted()
        .into_iter()
        .zip(&mut proof.openings)
    {
        *opening = super::wire::FibreOpening::empty();
        let u = FibreIndex::new(u as usize).unwrap();
        c1.fill_opening(u, opening);
        c2.fill_opening(u, opening);
    }
}
#[test]
#[ignore = "full 29 x 2^20 words, optimized release on a capped build host"]
fn full_size_roundtrip_corruption_and_domain_identity() {
    assert!(!cfg!(debug_assertions), "full-size gate is release-only");
    let start = Instant::now();
    let basis = NaturalBasis::new(BasisSize::Initial).unwrap();
    let domain = EncodingDomain::new().unwrap();
    let messages = honest_messages();
    let c1 = Commitment::new(hash, &domain, CommitmentTime::C1, &messages).unwrap();
    // C1 exists before rows 0/1. H1/G could be generated with their challenges.
    let mut st = SemanticTranscript::new(hash, &public(), c1.root()).unwrap();
    st.sample(SemanticMessage::None).unwrap();
    st.sample(SemanticMessage::None).unwrap();
    let c2 = Commitment::new(hash, &domain, CommitmentTime::C2, &messages).unwrap();
    st.sample(SemanticMessage::C2Root(c2.root())).unwrap();
    for row in 3..25 {
        let h = fields::<28>(row);
        let m = match row {
            14 => SemanticMessage::MaskSum(value(14, 0)),
            15..=24 => SemanticMessage::RoundPolynomial(&h),
            _ => SemanticMessage::None,
        };
        st.sample(m).unwrap();
    }
    let points = opening::points_from_alphas(&core::array::from_fn(|j| st.challenges()[15 + j]));
    let claims = prover::honest_claims(&messages, &points).unwrap();
    let boundary = st.finish(claims, true).unwrap();
    println!(
        "full_size_commitments_seconds={:.6}",
        start.elapsed().as_secs_f64()
    );
    let prove_start = Instant::now();
    let proof = prover::prove(hash, &basis, &boundary, &messages, &c1, &c2).unwrap();
    let bytes = proof.encode().unwrap();
    println!(
        "opening_prover_seconds={:.6} proof_bytes={}",
        prove_start.elapsed().as_secs_f64(),
        bytes.len()
    );
    let verify_start = Instant::now();
    verifier::verify(hash, &basis, &boundary, &bytes).unwrap();
    println!(
        "opening_verifier_seconds={:.6}",
        verify_start.elapsed().as_secs_f64()
    );
    let p = verifier::prepare(hash, &boundary, &proof).unwrap();
    let c = &p.challenges;
    let mut q = [E::ZERO; 1024];
    let gp = opening::powers::<29>(c.gamma);
    for l in 0..29 {
        let ql = prover::quotient(&basis, p.data.z, &messages[l], proof.y[l]).unwrap();
        for r in 0..1024 {
            q[r] = q[r].add(gp[l].mul(ql[r]));
        }
    }
    assert_eq!(fold::fold_message(c.alpha, &q), proof.final_message);
    // Full-domain equation (every point) for a full-support K message.
    let domain_start = Instant::now();
    let lane = 28;
    let ql = prover::quotient(&basis, p.data.z, &messages[lane], proof.y[lane]).unwrap();
    let iw = chord::interpolant(p.data.z[0], p.data.z[1], proof.y[lane]).unwrap();
    let wq = domain.encode(&ql.map(|x| x.c0())).unwrap();
    let wt = domain.encode(&messages[lane].map(|x| x.c0())).unwrap();
    let line = p.data.line();
    for u in 0..super::FIBRE_COUNT {
        let u = FibreIndex::new(u).unwrap();
        let z = domain::fibre_point::<crate::field::QM31>(u);
        for (s, (x, y)) in [
            (z.x, z.y),
            (z.x, z.y.neg()),
            (z.x.neg(), z.y.neg()),
            (z.x.neg(), z.y),
        ]
        .into_iter()
        .enumerate()
        {
            let idx = 4 * u.get() + s;
            let l = line.a.c0().add(line.b.c0().mul(x)).add(line.c.c0().mul(y));
            let i = iw[0].c0().add(iw[2].c0().mul(x)).add(iw[1].c0().mul(y));
            assert_eq!(wq[idx].mul(l), wt[idx].sub(i));
        }
    }
    for idx in [0, 1, 2, 3, 4, 4097, 1048575] {
        assert_eq!(
            E::from_qm31(wt[idx]),
            encoder::exact_initial_encoder(&messages[lane], InitialIndex::new(idx).unwrap())
        );
    }
    println!(
        "whole_domain_quotient_identity_seconds={:.6}",
        domain_start.elapsed().as_secs_f64()
    );
    drop(wq);
    drop(wt);
    // Single-record wire flips must all reject. Header changes also move S,
    // so their untouched authentication paths are normally the first failure.
    for kind in 0..6 {
        let mut bad = proof.clone();
        let mut b = boundary.clone();
        match kind {
            0 => bad.openings[0].values[0][0] = bad.openings[0].values[0][0].add(E::ONE),
            1 => bad.final_message[0] = bad.final_message[0].add(E::ONE),
            2 => bad.y[0][1] = bad.y[0][1].add(E::ONE),
            3 => bad.v = bad.v.add(E::ONE),
            4 => bad.coefficients[2] = bad.coefficients[2].add(E::ONE),
            _ => {
                let mut roots = b.roots();
                roots[0][0] ^= 1;
                b = SemanticBoundary::from_verified_parts(
                    b.state(),
                    roots,
                    *b.challenges(),
                    b.claims,
                    true,
                )
                .unwrap();
            }
        }
        assert_eq!(
            verifier::verify(hash, &basis, &b, &bad.encode().unwrap()).unwrap_err(),
            Error::Authentication,
            "wire corruption {kind}"
        );
    }
    // Reauthenticate after a corrupt F so a real full verifier reaches V1.
    let mut bad = proof.clone();
    bad.final_message[0] = bad.final_message[0].add(E::ONE);
    reopen(&mut bad, &boundary, &c1, &c2);
    assert_eq!(
        verifier::verify(hash, &basis, &boundary, &bad.encode().unwrap()).unwrap_err(),
        Error::V1
    );
    // A bad Y with correct authentication also reaches V1.
    let mut bad = proof.clone();
    bad.y[0][1] = bad.y[0][1].add(E::ONE);
    reopen(&mut bad, &boundary, &c1, &c2);
    assert_eq!(
        verifier::verify(hash, &basis, &boundary, &bad.encode().unwrap()).unwrap_err(),
        Error::V1
    );
    // v and each transmitted c_i: recompute the honest F at the new alpha
    // and authenticate new S. V1 passes; V2 must reject the false identity.
    for kind in 0..7 {
        let mut bad = proof.clone();
        if kind == 0 {
            bad.v = bad.v.add(E::ONE);
        } else {
            bad.coefficients[kind - 1] = bad.coefficients[kind - 1].add(E::ONE);
        }
        let changed = verifier::prepare(hash, &boundary, &bad).unwrap();
        bad.final_message = fold::fold_message(changed.challenges.alpha, &q);
        reopen(&mut bad, &boundary, &c1, &c2);
        assert_eq!(
            verifier::verify(hash, &basis, &boundary, &bad.encode().unwrap()).unwrap_err(),
            Error::V2,
            "isolated V2 corruption {kind}"
        );
    }
    // Independent fixed-challenge predicates: bad opened value leaves V2
    // true, bad polynomial leaves V1 true. These helpers never authenticate.
    let u = FibreIndex::new(c.queries.sorted()[0] as usize).unwrap();
    let mut bad = proof.openings[0].clone();
    bad.values[0][0] = bad.values[0][0].add(E::ONE);
    assert_eq!(
        verifier::check_v1(&p.data, c.gamma, c.alpha, &proof.final_message, u, &bad),
        Err(Error::V1)
    );
    verifier::check_v2(
        &basis,
        &p.data,
        c.kappa,
        c.tau,
        c.alpha,
        &p.polynomial,
        &proof.final_message,
    )
    .unwrap();
    let mut pc = p.polynomial;
    pc[0] = pc[0].add(E::ONE);
    verifier::check_v1(
        &p.data,
        c.gamma,
        c.alpha,
        &proof.final_message,
        u,
        &proof.openings[0],
    )
    .unwrap();
    assert_eq!(
        verifier::check_v2(
            &basis,
            &p.data,
            c.kappa,
            c.tau,
            c.alpha,
            &pc,
            &proof.final_message
        ),
        Err(Error::V2)
    );
    if let Ok(dir) = std::env::var("R0_EVIDENCE_DIR") {
        std::fs::write(format!("{dir}/honest-proof.bin"), &bytes).unwrap();
        std::fs::write(format!("{dir}/fixture.json"),serde_json::to_vec_pretty(&serde_json::json!({"roots":boundary.roots().map(|r|hex(&r)),"semantic_state":hex(&boundary.state()),"final_state":hex(&p.transcript_state),"proof_sha256":hex(&hash(&[&bytes])),"proof_bytes":bytes.len(),"queries_ordered":c.queries.ordered(),"semantic_fixture":"synthetic accepted boundary; no payment semantics claimed"})).unwrap()).unwrap();
    }
    println!("full_size_gate_seconds={:.6}; 6 wire corruptions, F/Y V1, v/all-six-ci V2, independent V1/V2: PASS",start.elapsed().as_secs_f64());
}
