//! Literal sampler control-flow tests. These mock hashes are not a random
//! oracle or the generated host; no probability claim follows from them.
use aspis_core::transcript::{QuerySampleError, Transcript};

fn stream(inputs: &[&[u8]], candidate: fn(usize) -> u32) -> [u8; 32] {
    let input: Vec<u8> = inputs
        .iter()
        .flat_map(|part| part.iter().copied())
        .collect();
    assert_eq!(input.len(), 33);
    let block = input[0] as usize;
    match input[32] {
        1 => {
            let mut answer = [0; 32];
            for i in 0..8 {
                answer[4 * i..4 * i + 4].copy_from_slice(&candidate(8 * block + i).to_le_bytes());
            }
            answer
        }
        2 => {
            let mut state: [u8; 32] = input[..32].try_into().unwrap();
            state[0] += 1;
            state
        }
        _ => panic!("unexpected operation"),
    }
}

fn last_draw(inputs: &[&[u8]]) -> [u8; 32] {
    stream(inputs, |i| match i {
        0..=20 => i as u32,
        63 => 21,
        _ => 0,
    })
}

fn too_late(inputs: &[&[u8]]) -> [u8; 32] {
    stream(inputs, |i| match i {
        0..=20 => i as u32,
        64 => 21,
        _ => 0,
    })
}

fn boundary(inputs: &[&[u8]]) -> [u8; 32] {
    // Two duplicate zeros: the 22nd distinct value is candidate 24.
    stream(inputs, |i| i.saturating_sub(2) as u32)
}

fn high_bits(inputs: &[&[u8]]) -> [u8; 32] {
    stream(inputs, |i| (i as u32) | 0xfffc0000)
}

#[test]
fn r15_q22_accepts_last_draw_but_never_draw_65() {
    let mut t = Transcript::new(last_draw);
    assert_eq!(
        t.challenge_queries_without_replacement(22, 1 << 18, 64),
        Ok((0..22).collect())
    );
    let mut t = Transcript::new(too_late);
    assert_eq!(
        t.challenge_queries_without_replacement(22, 1 << 18, 64),
        Err(QuerySampleError::DrawLimitExhausted {
            accepted: 21,
            max_draws: 64
        })
    );
    // The first word of the next block is the otherwise-successful candidate.
    assert_eq!(
        u32::from_le_bytes(t.squeeze_block()[..4].try_into().unwrap()),
        21
    );
}

#[test]
fn r15_q22_boundary_success_consumes_an_extra_block() {
    let mut t = Transcript::new(boundary);
    assert_eq!(
        t.challenge_queries_without_replacement(22, 1 << 18, 64),
        Ok((0..22).collect())
    );
    // Success at candidate 24 consumes block 4 before checking out.len().
    // The next squeeze therefore starts with candidate index 32, not 24.
    assert_eq!(
        u32::from_le_bytes(t.squeeze_block()[..4].try_into().unwrap()),
        30
    );
}

#[test]
fn r15_q22_masks_high_bits_and_discards_unused_block_words() {
    let mut t = Transcript::new(high_bits);
    assert_eq!(
        t.challenge_queries_without_replacement(22, 1 << 18, 64),
        Ok((0..22).collect())
    );
    assert_eq!(
        u32::from_le_bytes(t.squeeze_block()[..4].try_into().unwrap()) & ((1 << 18) - 1),
        24
    );
}
