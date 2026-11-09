extern crate std;

use super::*;
use num_bigint::BigUint;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{cell::RefCell, vec, vec::Vec};

fn kats() -> Value {
    serde_json::from_str(include_str!(
        "../../../../results/r0-samplers-20261009/kats.json"
    ))
    .unwrap()
}

fn hex(value: &Value) -> Vec<u8> {
    value
        .as_str()
        .unwrap()
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

fn numbers<const N: usize>(value: &Value) -> [u32; N] {
    let values = value.as_array().unwrap();
    assert_eq!(values.len(), N);
    core::array::from_fn(|i| u32::try_from(values[i].as_u64().unwrap()).unwrap())
}

fn qm_limbs(q: QM31) -> [u32; 4] {
    [q.c0.a.0, q.c0.b.0, q.c1.a.0, q.c1.b.0]
}

fn check_circle(point: SecureCirclePoint, expected: &Value) {
    assert_eq!(qm_limbs(point.x), numbers::<4>(&expected["x"]));
    assert_eq!(qm_limbs(point.y), numbers::<4>(&expected["y"]));
    assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
}

fn big(rank: Rank) -> BigUint {
    BigUint::new(rank.to_vec())
}

fn block(n: &BigUint) -> [u8; 32] {
    let bytes = n.to_bytes_le();
    let mut block = [0; 32];
    block[..bytes.len()].copy_from_slice(&bytes);
    block
}

fn from_digits(digits: &[u32]) -> BigUint {
    digits
        .iter()
        .rev()
        .fold(BigUint::from(0u32), |n, d| n * P + BigUint::from(*d))
}

#[test]
fn fixed_blocks_match_independent_python_bigint_kats() {
    let vectors = kats();
    let p = BigUint::from(P);
    assert_eq!(big(P4), p.pow(4));
    assert_eq!(big(P8), p.pow(8));
    assert_eq!(big(P8_MINUS_ONE), p.pow(8) - 1u32);
    for kat in vectors["samplers"].as_array().unwrap() {
        let bytes: [u8; 32] = hex(&kat["block_hex"]).try_into().unwrap();
        assert_eq!(
            big(block_rank(&bytes)),
            kat["rank"].as_str().unwrap().parse::<BigUint>().unwrap(),
            "{}",
            kat["name"]
        );
        for (modulus, key) in [
            (P4, "mod_p4"),
            (P8, "mod_p8"),
            (P8_MINUS_ONE, "mod_p8_minus_one"),
        ] {
            assert_eq!(
                big(reduce_rank(block_rank(&bytes), modulus)),
                kat[key].as_str().unwrap().parse::<BigUint>().unwrap()
            );
        }
        assert_eq!(qm_limbs(qm31_sample(&bytes)), numbers::<4>(&kat["qm31"]));
        assert_eq!(
            ordinary_sample(&bytes).to_limbs(),
            numbers::<8>(&kat["ordinary"])
        );
        assert_eq!(gamma_sample(&bytes).to_limbs(), numbers::<8>(&kat["gamma"]));
        assert!(!gamma_sample(&bytes).is_zero());
        check_circle(circle_sample(&bytes, CircleRow::First), &kat["circle0"]);
        check_circle(circle_sample(&bytes, CircleRow::Second), &kat["circle1"]);
    }
}

fn check_bigint(bytes: [u8; 32]) {
    let rank = block_rank(&bytes);
    let n = BigUint::from_bytes_le(&bytes);
    assert_eq!(big(rank), n);
    assert_eq!(block(&big(rank)), bytes);
    for modulus in [P4, P8, P8_MINUS_ONE] {
        let reduced = reduce_rank(rank, modulus);
        assert_eq!(big(reduced), &n % big(modulus));
        let digits = base_p_digits(reduced);
        assert!(digits.iter().all(|&d| d < P));
        assert_eq!(from_digits(&digits), big(reduced));
        let field = decode8(digits);
        assert_eq!(field.to_limbs(), digits);
        assert_eq!(WideExact::from_limbs(digits), Some(field));
        assert_eq!(WideExact::from_le_bytes(&field.to_le_bytes()), Some(field));
    }
    assert_eq!(from_digits(&qm_limbs(qm31_sample(&bytes))), &n % big(P4));
    assert_eq!(
        from_digits(&ordinary_sample(&bytes).to_limbs()),
        &n % big(P8)
    );
    assert_eq!(
        from_digits(&gamma_sample(&bytes).to_limbs()),
        &n % big(P8_MINUS_ONE) + 1u32
    );
    assert!(!gamma_sample(&bytes).is_zero());
}

#[test]
fn modular_reduction_and_digit_limb_roundtrips_bigint_oracle() {
    check_bigint([0; 32]);
    check_bigint([255; 32]);
    // Every bit and carry boundary, plus multiples of the actual divisors.
    for bit in 0usize..256 {
        let power = BigUint::from(1u32) << bit;
        for n in [&power - 1u32, power.clone(), &power + 1u32] {
            check_bigint(block(&n));
        }
    }
    for modulus in [P4, P8, P8_MINUS_ONE] {
        for multiple in [1u32, 2, 17, 255, 256] {
            let n = big(modulus) * multiple;
            for n in [&n - 1u32, n.clone(), &n + 1u32] {
                check_bigint(block(&n));
            }
        }
    }
    for seed in 0..2048u32 {
        let bytes: [u8; 32] = Sha256::digest(seed.to_le_bytes()).into();
        check_bigint(bytes);
    }
    // Rank and the canonical field byte encoding are deliberately different.
    let d = [1, 2, 3, 4, 5, 6, 7, 8];
    assert_eq!(ordinary_sample(&block(&from_digits(&d))).to_limbs(), d);
    assert_ne!(block(&from_digits(&d)), decode8(d).to_le_bytes());
}

#[test]
fn gamma_zero_and_ff_are_nonzero_and_circle_poles_use_each_fallback() {
    assert_eq!(gamma_sample(&[0; 32]), WideExact::ONE);
    assert!(!gamma_sample(&[255; 32]).is_zero());
    let p = BigUint::from(P);
    for n in [
        BigUint::from(0u32),
        BigUint::from(1u32),
        p.clone(),
        &p * (P - 1),
    ] {
        let bytes = block(&n);
        for (row, sample) in [(CircleRow::First, 0), (CircleRow::Second, 1)] {
            assert_eq!(circle_sample(&bytes, row), circle_fallback_point(sample));
        }
    }
    assert_ne!(circle_fallback_point(0), circle_fallback_point(1));
}

#[derive(Default)]
struct Script {
    blocks: Vec<[u8; 32]>,
    calls: Vec<Vec<u8>>,
}

std::thread_local! {
    static SCRIPT: RefCell<Script> = RefCell::new(Script::default());
}

fn set_blocks(blocks: Vec<[u8; 32]>) {
    SCRIPT.with(|script| {
        *script.borrow_mut() = Script {
            blocks,
            calls: Vec::new(),
        }
    });
}

// Each advance increments state[0]. Squeezes use that index. The backend
// records every hash preimage, so extra absorbs/blocks cannot hide behind
// equality of returned field values.
fn scripted_hash(inputs: &[&[u8]]) -> [u8; 32] {
    let input: Vec<u8> = inputs.iter().flat_map(|x| x.iter().copied()).collect();
    SCRIPT.with(|script| {
        let mut script = script.borrow_mut();
        script.calls.push(input.clone());
        let mut state: [u8; 32] = input[..32].try_into().unwrap();
        match input[32] {
            0 => {
                state[1] += 1;
                state[2] = input[33];
                state
            }
            1 => script.blocks[state[0] as usize],
            2 => {
                state[0] += 1;
                state
            }
            _ => panic!("unexpected domain"),
        }
    })
}

fn state_after(t: &Transcript, count: u8) {
    let mut expected = [0; 32];
    expected[0] = count;
    assert_eq!(t.diagnostic_state(), expected);
}

#[test]
fn query_python_kats_and_legacy_agree_on_every_stop_position_and_state() {
    for kat in kats()["queries"].as_array().unwrap() {
        let blocks: Vec<[u8; 32]> = kat["blocks_hex"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| hex(v).try_into().unwrap())
            .collect();
        let accepted: Vec<u32> = kat["accepted"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap() as u32)
            .collect();
        let count = kat["blocks"].as_u64().unwrap() as u8;
        let expected = if kat["ok"].as_bool().unwrap() {
            Ok(accepted.clone().try_into().unwrap())
        } else {
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: accepted.len(),
                max_draws: 64,
            })
        };
        let mut scan = QueryScan::default();
        for (i, bytes) in blocks.iter().take(count as usize).enumerate() {
            let stopped = scan.scan(bytes);
            assert_eq!(
                stopped,
                i + 1 == count as usize && kat["draws"].as_u64().unwrap() < 64
            );
        }
        assert_eq!(scan.draws, kat["draws"].as_u64().unwrap() as usize);
        assert_eq!(&scan.accepted[..scan.accepted_len], accepted);
        assert_eq!(scan.finish(), expected);

        set_blocks(blocks.clone());
        let mut r0 = Transcript::new(scripted_hash);
        assert_eq!(r0.r0_challenge_queries(), expected, "{}", kat["name"]);
        state_after(&r0, count);
        SCRIPT.with(|s| {
            let s = s.borrow();
            assert_eq!(s.calls.len(), 2 * count as usize);
            for (index, pair) in s.calls.chunks_exact(2).enumerate() {
                assert_eq!((pair[0][32], pair[1][32]), (1, 2));
                assert_eq!(pair[0][0], index as u8);
                assert_eq!(&pair[0][..32], &pair[1][..32]);
            }
        });
        set_blocks(blocks);
        let mut legacy = Transcript::new(scripted_hash);
        assert_eq!(
            legacy.challenge_queries_without_replacement(22, 1 << 18, 64),
            expected.map(|a| a.to_vec())
        );
        assert_eq!(legacy.diagnostic_state(), r0.diagnostic_state());
    }
}

#[test]
fn query_draw_65_cannot_rescue_exhaustion_and_no_word_consumed_after_stop() {
    let mut scan = QueryScan::default();
    for _ in 0..8 {
        assert!(!scan.scan(&[0; 32]));
    }
    assert_eq!((scan.draws, scan.accepted_len), (64, 1));
    assert!(scan.scan(&[255; 32]));
    assert_eq!((scan.draws, scan.accepted_len), (64, 1));

    let mut words = [0u32; 72];
    for (i, word) in words[..21].iter_mut().enumerate() {
        *word = i as u32;
    }
    words[64] = 21;
    let blocks = words
        .chunks_exact(8)
        .map(|words| core::array::from_fn(|j| words[j / 4].to_le_bytes()[j % 4]))
        .collect();
    set_blocks(blocks);
    let mut t = Transcript::new(scripted_hash);
    assert_eq!(
        t.r0_challenge_queries(),
        Err(QuerySampleError::DrawLimitExhausted {
            accepted: 21,
            max_draws: 64
        })
    );
    state_after(&t, 8);
    assert_eq!(query_words(&t.squeeze_block())[0], 21);
}

#[test]
fn every_field_and_circle_primitive_consumes_exactly_one_block() {
    for kat in kats()["samplers"].as_array().unwrap() {
        let bytes: [u8; 32] = hex(&kat["block_hex"]).try_into().unwrap();
        for method in 0..5 {
            set_blocks(vec![bytes]);
            let mut t = Transcript::new(scripted_hash);
            match method {
                0 => assert_eq!(t.r0_challenge_qm31(), qm31_sample(&bytes)),
                1 => assert_eq!(t.r0_challenge_ordinary(), ordinary_sample(&bytes)),
                2 => assert_eq!(t.r0_challenge_gamma(), gamma_sample(&bytes)),
                3 => assert_eq!(
                    t.r0_challenge_circle(CircleRow::First),
                    circle_sample(&bytes, CircleRow::First)
                ),
                _ => assert_eq!(
                    t.r0_challenge_circle(CircleRow::Second),
                    circle_sample(&bytes, CircleRow::Second)
                ),
            }
            state_after(&t, 1);
            SCRIPT.with(|s| {
                let s = s.borrow();
                assert_eq!(s.calls.len(), 2);
                assert_eq!(s.calls[0], [&[0; 32][..], &[1]].concat());
                assert_eq!(s.calls[1], [&[0; 32][..], &[2]].concat());
            });
        }
    }
}

fn hash(inputs: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for input in inputs {
        h.update(input);
    }
    h.finalize().into()
}

#[test]
fn provisional_32_row_framing_matches_independent_sha256_kat() {
    let mut t = Transcript::new(hash);
    for kat in kats()["rows"].as_array().unwrap() {
        let row = kat["row"].as_u64().unwrap() as u8;
        let message = hex(&kat["message_hex"]);
        let mut direct = t.clone();
        direct.absorb(kat["label"].as_u64().unwrap() as u8, &message);
        assert_eq!(
            direct.diagnostic_state().as_slice(),
            hex(&kat["post_absorb_hex"])
        );
        let result = &kat["result"];
        match t.r0_sample_row(row, &message).unwrap() {
            R0Challenge::Qm31(q) => {
                assert_eq!(result["kind"], "qm31");
                assert_eq!(qm_limbs(q), numbers::<4>(&result["value"]));
            }
            R0Challenge::Circle(point) => {
                assert!(row == 25 || row == 26);
                check_circle(point, &result["value"]);
            }
            R0Challenge::Wide(w) => {
                assert_eq!(result["kind"], if row == 27 { "gamma" } else { "ordinary" });
                assert_eq!(w.to_limbs(), numbers::<8>(&result["value"]));
            }
            R0Challenge::Queries(q) => {
                assert_eq!(row, 31);
                assert_eq!(q, numbers::<22>(&result["accepted"]));
            }
        }
        assert_eq!(
            t.diagnostic_state().as_slice(),
            hex(&kat["state_hex"]),
            "row {row}"
        );
    }
}

#[test]
fn every_row_absorbs_once_even_empty_and_invalid_rows_do_nothing() {
    for row in 0..32 {
        for length in [0, 1, 158, 159, 512] {
            set_blocks(vec![[0; 32]; 8]);
            let mut t = Transcript::new(scripted_hash);
            let message = vec![0x7a; length];
            let result = t.r0_sample_row(row, &message);
            if row == 31 {
                assert_eq!(
                    result,
                    Err(R0RowError::Queries(QuerySampleError::DrawLimitExhausted {
                        accepted: 1,
                        max_draws: 64
                    }))
                );
            } else {
                assert!(result.is_ok());
            }
            SCRIPT.with(|s| {
                let s = s.borrow();
                let count = if row == 31 { 8 } else { 1 };
                assert_eq!(s.calls.len(), 1 + 2 * count);
                let first = &s.calls[0];
                assert_eq!(&first[..32], &[0; 32]);
                assert_eq!(&first[32..34], &[0, 0x80 + row]);
                assert_eq!(&first[34..], message);
                for pair in s.calls[1..].chunks_exact(2) {
                    assert_eq!((pair[0][32], pair[1][32]), (1, 2));
                    assert_eq!(&pair[0][..32], &pair[1][..32]);
                }
                let mut expected = [0; 32];
                expected[0] = count as u8;
                expected[1] = 1;
                expected[2] = 0x80 + row;
                assert_eq!(t.diagnostic_state(), expected);
            });
        }
    }
    for row in 32..=255 {
        set_blocks(Vec::new());
        let mut t = Transcript::new(scripted_hash);
        assert_eq!(label::R0_ROW(row), None);
        assert_eq!(
            t.r0_sample_row(row, &[]),
            Err(R0RowError::InvalidRow { row })
        );
        state_after(&t, 0);
        SCRIPT.with(|s| assert!(s.borrow().calls.is_empty()));
    }
}

#[test]
fn arbitrary_blocks_and_row_paths_do_not_panic() {
    for seed in 0..256u32 {
        let bytes: [u8; 32] = Sha256::digest(seed.to_le_bytes()).into();
        std::panic::catch_unwind(|| {
            for row in 0..32 {
                set_blocks(vec![bytes; 8]);
                let mut t = Transcript::new(scripted_hash);
                let _ = t.r0_sample_row(row, &bytes);
            }
        })
        .expect("R0 sampler path panicked");
    }
}
