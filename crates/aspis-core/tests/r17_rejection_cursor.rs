//! Actual-core differential checks for the retained sequential cursor model.
//! Exhaustive over bounded retry schedules, NOT over values or oracle histories.
//! The scripted backend is deterministic by input; this is not an RO-law test.
use aspis_core::field::{P, QM31};
use aspis_core::transcript::{Transcript, CHALLENGE_RETRY_LIMIT};
use std::cell::RefCell;

#[derive(Default)]
struct Script {
    words: Vec<u32>,
    calls: Vec<(usize, u8)>,
}
thread_local! { static SCRIPT: RefCell<Script> = RefCell::new(Script::default()); }

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let input: Vec<u8> = parts.iter().flat_map(|p| p.iter().copied()).collect();
    assert_eq!(input.len(), 33);
    assert!(input[8..32].iter().all(|&b| b == 0));
    let index = u64::from_le_bytes(input[..8].try_into().unwrap()) as usize;
    let domain = input[32];
    SCRIPT.with(|s| {
        let mut s = s.borrow_mut();
        s.calls.push((index, domain));
        let mut out = [0; 32];
        match domain {
            1 => {
                for (slot, word) in out
                    .chunks_exact_mut(4)
                    .zip(&s.words[index * 8..(index + 1) * 8])
                {
                    slot.copy_from_slice(&word.to_le_bytes());
                }
            }
            2 => out[..8].copy_from_slice(&((index + 1) as u64).to_le_bytes()),
            _ => panic!("unexpected domain {domain}"),
        }
        out
    })
}

// Operational counterpart of scanMany: one shared cursor, resetting only
// the per-limb attempt budget. A short input is a fixture error, not an abort.
fn cursor_model(words: &[u32]) -> (Option<[u32; 4]>, usize) {
    let mut cursor = 0;
    let mut values = [0; 4];
    for value in &mut values {
        let candidates = &words[cursor..cursor + 8];
        match candidates.iter().position(|w| w & P != P) {
            Some(rejected) => {
                *value = candidates[rejected] & P;
                cursor += rejected + 1;
            }
            None => return (None, cursor + 8),
        }
    }
    (Some(values), cursor)
}

fn limbs(q: QM31) -> [u32; 4] {
    [q.c0.a.0, q.c0.b.0, q.c1.a.0, q.c1.b.0]
}

fn check_schedule(rejections: &[usize], exhaust: bool, high_bit_phase: usize) {
    assert_eq!(CHALLENGE_RETRY_LIMIT, 8, "pinned model budget changed");
    let accepted = [0, 1, P - 1, 0x0123_4567];
    let mut words: Vec<u32> = (0..48).map(|i| 0x0203_0405 + i).collect();
    let mut cursor = 0;
    for (limb, &rejected) in rejections.iter().enumerate() {
        words[cursor..cursor + rejected].fill(P);
        cursor += rejected;
        words[cursor] = accepted[limb];
        cursor += 1;
    }
    if exhaust {
        words[cursor..cursor + 8].fill(P);
        cursor += 8;
    }
    // Both encodings of every masked candidate occur across the two runs.
    // Rejected words include both 0x7fffffff and 0xffffffff.
    for (i, word) in words.iter_mut().enumerate() {
        *word |= (((i + high_bit_phase) % 2) as u32) << 31;
    }
    let (expected, used) = cursor_model(&words);
    assert_eq!(used, cursor);
    assert_eq!(expected.is_none(), exhaust);
    if !exhaust {
        assert_eq!(expected, Some(accepted));
    }
    let blocks = used.div_ceil(8);
    let (next_expected, next_used) = cursor_model(&words[blocks * 8..]);
    assert_eq!(next_used, 4);
    SCRIPT.with(|s| {
        *s.borrow_mut() = Script {
            words,
            calls: Vec::new(),
        }
    });
    let mut transcript = Transcript::new(hash);
    assert_eq!(transcript.challenge_qm31().ok().map(limbs), expected);
    let mut expected_state = [0; 32];
    expected_state[..8].copy_from_slice(&(blocks as u64).to_le_bytes());
    assert_eq!(transcript.diagnostic_state(), expected_state);
    SCRIPT.with(|s| {
        let s = s.borrow();
        let expected_calls: Vec<_> = (0..blocks).flat_map(|i| [(i, 1), (i, 2)]).collect();
        assert_eq!(s.calls, expected_calls);
    });
    // A new call starts a new block, not at the previous unconsumed word.
    // This also checks the retained transcript state after an explicit abort.
    assert_eq!(transcript.challenge_qm31().ok().map(limbs), next_expected);
    expected_state[..8].copy_from_slice(&((blocks + 1) as u64).to_le_bytes());
    assert_eq!(transcript.diagnostic_state(), expected_state);
    SCRIPT.with(|s| {
        let s = s.borrow();
        let expected_calls: Vec<_> = (0..=blocks).flat_map(|i| [(i, 1), (i, 2)]).collect();
        assert_eq!(s.calls, expected_calls);
    });
}

fn digits(mut code: usize, count: usize) -> Vec<usize> {
    (0..count)
        .map(|_| {
            let digit = code % 8;
            code /= 8;
            digit
        })
        .collect()
}

#[test]
fn every_successful_retry_schedule_matches_shared_cursor() {
    let mut checked = 0;
    for code in 0..8usize.pow(4) {
        for phase in 0..2 {
            check_schedule(&digits(code, 4), false, phase);
            checked += 1;
        }
    }
    assert_eq!(checked, 8192);
    println!("checked 4096 success schedules, both high-bit phases, next-call discard");
}

#[test]
fn every_reachable_limb_exhaustion_schedule_matches_shared_cursor() {
    let mut checked = 0;
    for preceding_limbs in 0..4 {
        for code in 0..8usize.pow(preceding_limbs) {
            for phase in 0..2 {
                check_schedule(&digits(code, preceding_limbs as usize), true, phase);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 1170);
    println!("checked 585 exhaustion schedules, both high-bit phases, post-abort state");
}
