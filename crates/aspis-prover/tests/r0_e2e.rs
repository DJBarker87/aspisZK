#![cfg(all(feature = "r0", feature = "insecure-spend-fixture"))]
use aspis_core::{
    field::WideExact as E,
    r0::{
        basis::{BasisSize, NaturalBasis},
        domain::FibreIndex,
        verifier,
        wire::OpeningProof,
        Error as OError,
    },
    state_only_prefix::r0::{self as sw, Error as SError},
};
use aspis_prover::{r0_fixture, HOST_HASH};
use aspis_statement::{
    r0::{self, Error},
    state_only_verify::r0::verify_semantics,
};
use serde_json::json;

#[test]
fn fixed_wire_size_and_exact_parser() {
    assert_eq!(r0::PROOF_BYTES, 95_712);
    assert!(r0::Proof::parse(&vec![0; r0::PROOF_BYTES - 1]).is_err());
    assert!(r0::Proof::parse(&vec![0; r0::PROOF_BYTES + 1]).is_err());
}

fn add_field(bytes: &mut [u8], at: usize) {
    let value = E::from_le_bytes(&bytes[at..at + 32]).unwrap().add(E::ONE);
    bytes[at..at + 32].copy_from_slice(&value.to_le_bytes());
}

/// Uses the saved honest fixtures; never regenerates expensive witnesses
/// merely to run another negative test. Run optimized on the build host.
#[test]
#[ignore = "requires R0_E2E_FIXTURE_DIR and an optimized capped build-host job"]
fn both_variants_roundtrip_and_corruption_teeth() {
    assert!(!cfg!(debug_assertions));
    let dir = std::path::PathBuf::from(std::env::var("R0_E2E_FIXTURE_DIR").unwrap());
    let mut records = Vec::new();
    for name in ["transfer", "withdrawal"] {
        let bytes = std::fs::read(dir.join(format!("{name}.proof.bin"))).unwrap();
        let public_bytes = std::fs::read(dir.join(format!("{name}.public.bin"))).unwrap();
        let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(
            &public_bytes,
        )
        .unwrap();
        let public = r0_fixture::statement_public(&statement);
        let checked = r0::r0_verify(public, &bytes, HOST_HASH, None).unwrap();
        let wire = r0::Proof::parse(&bytes).unwrap();
        assert_eq!(wire.encode().unwrap(), bytes);
        let semantic = verify_semantics(public, wire.semantic, HOST_HASH).unwrap();
        let boundary = r0::semantic_handoff(&semantic).unwrap();
        let proof = OpeningProof::parse(wire.opening).unwrap();
        let prepared = verifier::prepare(HOST_HASH, &boundary, &proof).unwrap();
        assert_eq!(checked.queries, prepared.challenges.queries);
        assert_eq!(boundary.roots(), [semantic.c1_root, semantic.c2_root]);
        assert_eq!(boundary.claims, semantic.claims);
        let mut reject = |label: String, changed: Vec<u8>| {
            let error = r0::r0_verify(public, &changed, HOST_HASH, None).unwrap_err();
            records.push(json!({"variant":name,"mutation":label,"rejection":format!("{error:?}")}));
            error
        };
        reject("truncated".into(), bytes[..bytes.len() - 1].to_vec());
        let mut changed = bytes.clone();
        changed.push(0);
        reject("trailing".into(), changed);
        let mut changed = bytes.clone();
        changed[0] ^= 1;
        reject("C1 root".into(), changed);
        // Every semantic row has its own framing rejection, including all
        // empty rows. Each sumcheck recurrence check has an isolated tooth.
        let mut offset = 32;
        for row in 0..=26u8 {
            let (_, size) = sw::row_shape(row).unwrap();
            for header in [0, 1] {
                let mut changed = bytes.clone();
                changed[offset + header] ^= 0x40;
                reject(
                    format!("row {row} {}", if header == 0 { "tag" } else { "length" }),
                    changed,
                );
            }
            if size > 0 {
                let mut changed = bytes.clone();
                if row == 2 {
                    changed[offset + 5] ^= 1;
                } else {
                    add_field(&mut changed, offset + 5);
                }
                let error = reject(format!("row {row} message"), changed);
                if (15..=24).contains(&row) {
                    assert_eq!(
                        error,
                        Error::Semantic(SError::Boundary {
                            round: (row - 15) as usize
                        })
                    );
                }
                if row >= 14 {
                    let mut changed = bytes.clone();
                    changed[offset + 5..offset + 9]
                        .copy_from_slice(&aspis_core::field::P.to_le_bytes());
                    assert!(matches!(
                        reject(format!("row {row} noncanonical"), changed),
                        Error::Semantic(SError::NonCanonical { .. })
                    ));
                }
            }
            if row == 25 {
                for claim in 0..87 {
                    let mut changed = bytes.clone();
                    add_field(&mut changed, offset + 5 + 32 * claim);
                    reject(
                        format!("claim point {} lane {}", claim / 29, claim % 29),
                        changed,
                    );
                }
            }
            offset += 5 + size;
        }
        // All opening transcript messages, coefficients, and F coordinates.
        offset = r0::OPENING_OFFSET;
        for (tag, count) in [(5, 29), (6, 58), (7, 1), (9, 6), (10, 256)] {
            for header in [0, 1] {
                let mut changed = bytes.clone();
                changed[offset + header] ^= 0x40;
                reject(format!("opening tag {tag} header {header}"), changed);
            }
            for field in 0..count {
                let mut changed = bytes.clone();
                add_field(&mut changed, offset + 5 + field * 32);
                reject(format!("opening tag {tag} field {field}"), changed);
            }
            let mut changed = bytes.clone();
            changed[offset + 5..offset + 9].copy_from_slice(&aspis_core::field::P.to_le_bytes());
            reject(format!("opening tag {tag} noncanonical"), changed);
            offset += 5 + count * 32;
        }
        for header in [0, 1] {
            let mut changed = bytes.clone();
            changed[offset + header] ^= 0x40;
            reject(format!("authentication header {header}"), changed);
        }
        // Each sampled fibre and both root paths, all six levels. Leaves
        // cover every slot and lane (including C1-time D and C2 H1/G).
        for fibre in 0..22 {
            let start = offset + 5 + fibre * aspis_core::r0::wire::FIBRE_BYTES;
            for tree in 0..2 {
                for level in 0..6 {
                    let mut changed = bytes.clone();
                    changed[start + 608 + tree * 1344 + level * 224] ^= 1;
                    assert_eq!(
                        reject(format!("fibre {fibre} tree {tree} level {level}"), changed),
                        Error::Opening(OError::Authentication)
                    );
                }
            }
            let mut at = start;
            for slot in 0..4 {
                for lane in 0..29 {
                    if fibre == 0 || (slot == 0 && lane == 0) {
                        let mut changed = bytes.clone();
                        let v = u32::from_le_bytes(changed[at..at + 4].try_into().unwrap());
                        changed[at..at + 4]
                            .copy_from_slice(&((v + 1) % aspis_core::field::P).to_le_bytes());
                        assert_eq!(
                            reject(
                                format!("leaf fibre {fibre} slot {slot} lane {lane}"),
                                changed
                            ),
                            Error::Opening(OError::Authentication)
                        );
                    }
                    at += if lane < 26 { 4 } else { 16 };
                }
            }
        }
        // Independent checks with fixed transcript challenges: authentication
        // must not hide V1/V2 teeth behind the first failing predicate.
        let c = &prepared.challenges;
        let basis = NaturalBasis::new(BasisSize::Initial).unwrap();
        let u = FibreIndex::new(c.queries.sorted()[0] as usize).unwrap();
        let mut opening = proof.openings[0].clone();
        opening.values[0][28] = opening.values[0][28].add(E::ONE);
        assert_eq!(
            verifier::check_v1(
                &prepared.data,
                c.gamma,
                c.alpha,
                &proof.final_message,
                u,
                &opening
            ),
            Err(OError::V1)
        );
        verifier::check_v2(
            &basis,
            &prepared.data,
            c.kappa,
            c.tau,
            c.alpha,
            &prepared.polynomial,
            &proof.final_message,
        )
        .unwrap();
        records.push(json!({"variant":name,"mutation":"fixed-challenge D leaf","rejection":"V1; V2 remains true"}));
        for i in [0, 1, 2, 3, 5, 6] {
            let mut polynomial = prepared.polynomial;
            polynomial[i] = polynomial[i].add(E::ONE);
            if i == 0 {
                polynomial[4] = polynomial[4].sub(E::ONE);
            }
            assert_eq!(
                verifier::check_v2(
                    &basis,
                    &prepared.data,
                    c.kappa,
                    c.tau,
                    c.alpha,
                    &polynomial,
                    &proof.final_message
                ),
                Err(OError::V2)
            );
            records.push(json!({"variant":name,"mutation":format!("fixed-challenge coefficient {i}"),"rejection":"V2"}));
        }
        for i in 0..22 {
            verifier::check_v1(
                &prepared.data,
                c.gamma,
                c.alpha,
                &proof.final_message,
                FibreIndex::new(c.queries.sorted()[i] as usize).unwrap(),
                &proof.openings[i],
            )
            .unwrap();
        }
        // A changed public statement cannot reuse the transcript or proof.
        let mut changed = statement;
        match &mut changed {
            aspis_statement::pool_v1::PoolV1PairForestTerminalStatementV1::PrivateTransfer {
                public,
                ..
            } => public.asset_id = aspis_core::field::M31(78),
            aspis_statement::pool_v1::PoolV1PairForestTerminalStatementV1::Withdrawal {
                public,
                ..
            } => public.amount += 1,
        }
        assert!(r0::r0_verify(
            r0_fixture::statement_public(&changed),
            &bytes,
            HOST_HASH,
            None
        )
        .is_err());
        records.push(json!({"variant":name,"mutation":"public input","rejection":"end-to-end"}));
        eprintln!("{name}: round-trip, every row, all 87 claims, every opening coefficient, both paths per fibre and independent V1/V2 passed");
    }
    std::fs::write(
        dir.join("corruption-cases.json"),
        serde_json::to_vec_pretty(&records).unwrap(),
    )
    .unwrap();
    eprintln!("{} recorded rejection cases", records.len());
}
