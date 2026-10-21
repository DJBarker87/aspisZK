#[derive(Clone, Copy, Debug, kani::Arbitrary)]
pub struct TraceStep {
    pub output: u32,
    pub next_state: u64,
}

#[derive(Clone, Copy, Debug)]
pub struct Observation {
    pub index: usize,
    pub before: u64,
    pub after: u64,
    pub output: u32,
}

const EMPTY_OBSERVATION: Observation = Observation {
    index: 0,
    before: 0,
    after: 0,
    output: 0,
};

fn invoke<const N: usize>(trace: &[TraceStep; N], i: usize, state: &mut u64) -> (u32, Observation) {
    let before = *state;
    let entry = trace[i];
    *state = entry.next_state;
    (
        entry.output,
        Observation { index: i, before, after: *state, output: entry.output },
    )
}

fn run_from_fn<const N: usize>(trace: [TraceStep; N], initial: u64)
    -> ([u32; N], [Observation; N], u64, usize)
{
    let mut state = initial;
    let mut observations = [EMPTY_OBSERVATION; N];
    let mut calls = 0usize;
    let values = std::array::from_fn(|i| {
        let (value, event) = invoke(&trace, i, &mut state);
        observations[calls] = event;
        calls += 1;
        value
    });
    (values, observations, state, calls)
}

fn run_explicit4(trace: [TraceStep; 4], initial: u64)
    -> ([u32; 4], [Observation; 4], u64, usize)
{
    let mut state = initial;
    let (v0, e0) = invoke(&trace, 0, &mut state);
    let (v1, e1) = invoke(&trace, 1, &mut state);
    let (v2, e2) = invoke(&trace, 2, &mut state);
    let (v3, e3) = invoke(&trace, 3, &mut state);
    ([v0, v1, v2, v3], [e0, e1, e2, e3], state, 4)
}

fn run_explicit8(trace: [TraceStep; 8], initial: u64)
    -> ([u32; 8], [Observation; 8], u64, usize)
{
    let mut state = initial;
    let (v0, e0) = invoke(&trace, 0, &mut state);
    let (v1, e1) = invoke(&trace, 1, &mut state);
    let (v2, e2) = invoke(&trace, 2, &mut state);
    let (v3, e3) = invoke(&trace, 3, &mut state);
    let (v4, e4) = invoke(&trace, 4, &mut state);
    let (v5, e5) = invoke(&trace, 5, &mut state);
    let (v6, e6) = invoke(&trace, 6, &mut state);
    let (v7, e7) = invoke(&trace, 7, &mut state);
    ([v0, v1, v2, v3, v4, v5, v6, v7], [e0, e1, e2, e3, e4, e5, e6, e7], state, 8)
}

fn assert_obs_eq(a: Observation, b: Observation) {
    assert!(a.index == b.index);
    assert!(a.before == b.before);
    assert!(a.after == b.after);
    assert!(a.output == b.output);
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(16)]
fn std_from_fn_four_matches_explicit_ordered_calls() {
    let trace: [TraceStep; 4] = kani::any();
    let initial: u64 = kani::any();
    let actual = run_from_fn(trace, initial);
    let explicit = run_explicit4(trace, initial);
    assert!(actual.0[0] == explicit.0[0]);
    assert!(actual.0[1] == explicit.0[1]);
    assert!(actual.0[2] == explicit.0[2]);
    assert!(actual.0[3] == explicit.0[3]);
    assert_obs_eq(actual.1[0], explicit.1[0]);
    assert_obs_eq(actual.1[1], explicit.1[1]);
    assert_obs_eq(actual.1[2], explicit.1[2]);
    assert_obs_eq(actual.1[3], explicit.1[3]);
    assert!(actual.2 == explicit.2);
    assert!(actual.3 == explicit.3);
    }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(20)]
fn std_from_fn_eight_matches_explicit_ordered_calls() {
    let trace: [TraceStep; 8] = kani::any();
    let initial: u64 = kani::any();
    let actual = run_from_fn(trace, initial);
    let explicit = run_explicit8(trace, initial);
    assert!(actual.0[0] == explicit.0[0]);
    assert!(actual.0[1] == explicit.0[1]);
    assert!(actual.0[2] == explicit.0[2]);
    assert!(actual.0[3] == explicit.0[3]);
    assert!(actual.0[4] == explicit.0[4]);
    assert!(actual.0[5] == explicit.0[5]);
    assert!(actual.0[6] == explicit.0[6]);
    assert!(actual.0[7] == explicit.0[7]);
    assert_obs_eq(actual.1[0], explicit.1[0]);
    assert_obs_eq(actual.1[1], explicit.1[1]);
    assert_obs_eq(actual.1[2], explicit.1[2]);
    assert_obs_eq(actual.1[3], explicit.1[3]);
    assert_obs_eq(actual.1[4], explicit.1[4]);
    assert_obs_eq(actual.1[5], explicit.1[5]);
    assert_obs_eq(actual.1[6], explicit.1[6]);
    assert_obs_eq(actual.1[7], explicit.1[7]);
    assert!(actual.2 == explicit.2);
    assert!(actual.3 == explicit.3);
    }
fn run_explicit29(trace: [TraceStep; 29], initial: u64)
    -> ([u32; 29], [Observation; 29], u64, usize)
{
    let mut state = initial;
    let (v0, e0) = invoke(&trace, 0, &mut state);
    let (v1, e1) = invoke(&trace, 1, &mut state);
    let (v2, e2) = invoke(&trace, 2, &mut state);
    let (v3, e3) = invoke(&trace, 3, &mut state);
    let (v4, e4) = invoke(&trace, 4, &mut state);
    let (v5, e5) = invoke(&trace, 5, &mut state);
    let (v6, e6) = invoke(&trace, 6, &mut state);
    let (v7, e7) = invoke(&trace, 7, &mut state);
    let (v8, e8) = invoke(&trace, 8, &mut state);
    let (v9, e9) = invoke(&trace, 9, &mut state);
    let (v10, e10) = invoke(&trace, 10, &mut state);
    let (v11, e11) = invoke(&trace, 11, &mut state);
    let (v12, e12) = invoke(&trace, 12, &mut state);
    let (v13, e13) = invoke(&trace, 13, &mut state);
    let (v14, e14) = invoke(&trace, 14, &mut state);
    let (v15, e15) = invoke(&trace, 15, &mut state);
    let (v16, e16) = invoke(&trace, 16, &mut state);
    let (v17, e17) = invoke(&trace, 17, &mut state);
    let (v18, e18) = invoke(&trace, 18, &mut state);
    let (v19, e19) = invoke(&trace, 19, &mut state);
    let (v20, e20) = invoke(&trace, 20, &mut state);
    let (v21, e21) = invoke(&trace, 21, &mut state);
    let (v22, e22) = invoke(&trace, 22, &mut state);
    let (v23, e23) = invoke(&trace, 23, &mut state);
    let (v24, e24) = invoke(&trace, 24, &mut state);
    let (v25, e25) = invoke(&trace, 25, &mut state);
    let (v26, e26) = invoke(&trace, 26, &mut state);
    let (v27, e27) = invoke(&trace, 27, &mut state);
    let (v28, e28) = invoke(&trace, 28, &mut state);
    ([ v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28 ],
     [ e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28 ], state, 29)
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(48)]
fn std_from_fn_twenty_nine_matches_explicit_ordered_calls() {
    let trace: [TraceStep; 29] = kani::any();
    let initial: u64 = kani::any();
    let actual = run_from_fn(trace, initial);
    let explicit = run_explicit29(trace, initial);
    assert!(actual.0[0] == explicit.0[0]);
    assert!(actual.0[1] == explicit.0[1]);
    assert!(actual.0[2] == explicit.0[2]);
    assert!(actual.0[3] == explicit.0[3]);
    assert!(actual.0[4] == explicit.0[4]);
    assert!(actual.0[5] == explicit.0[5]);
    assert!(actual.0[6] == explicit.0[6]);
    assert!(actual.0[7] == explicit.0[7]);
    assert!(actual.0[8] == explicit.0[8]);
    assert!(actual.0[9] == explicit.0[9]);
    assert!(actual.0[10] == explicit.0[10]);
    assert!(actual.0[11] == explicit.0[11]);
    assert!(actual.0[12] == explicit.0[12]);
    assert!(actual.0[13] == explicit.0[13]);
    assert!(actual.0[14] == explicit.0[14]);
    assert!(actual.0[15] == explicit.0[15]);
    assert!(actual.0[16] == explicit.0[16]);
    assert!(actual.0[17] == explicit.0[17]);
    assert!(actual.0[18] == explicit.0[18]);
    assert!(actual.0[19] == explicit.0[19]);
    assert!(actual.0[20] == explicit.0[20]);
    assert!(actual.0[21] == explicit.0[21]);
    assert!(actual.0[22] == explicit.0[22]);
    assert!(actual.0[23] == explicit.0[23]);
    assert!(actual.0[24] == explicit.0[24]);
    assert!(actual.0[25] == explicit.0[25]);
    assert!(actual.0[26] == explicit.0[26]);
    assert!(actual.0[27] == explicit.0[27]);
    assert!(actual.0[28] == explicit.0[28]);
    assert_obs_eq(actual.1[0], explicit.1[0]);
    assert_obs_eq(actual.1[1], explicit.1[1]);
    assert_obs_eq(actual.1[2], explicit.1[2]);
    assert_obs_eq(actual.1[3], explicit.1[3]);
    assert_obs_eq(actual.1[4], explicit.1[4]);
    assert_obs_eq(actual.1[5], explicit.1[5]);
    assert_obs_eq(actual.1[6], explicit.1[6]);
    assert_obs_eq(actual.1[7], explicit.1[7]);
    assert_obs_eq(actual.1[8], explicit.1[8]);
    assert_obs_eq(actual.1[9], explicit.1[9]);
    assert_obs_eq(actual.1[10], explicit.1[10]);
    assert_obs_eq(actual.1[11], explicit.1[11]);
    assert_obs_eq(actual.1[12], explicit.1[12]);
    assert_obs_eq(actual.1[13], explicit.1[13]);
    assert_obs_eq(actual.1[14], explicit.1[14]);
    assert_obs_eq(actual.1[15], explicit.1[15]);
    assert_obs_eq(actual.1[16], explicit.1[16]);
    assert_obs_eq(actual.1[17], explicit.1[17]);
    assert_obs_eq(actual.1[18], explicit.1[18]);
    assert_obs_eq(actual.1[19], explicit.1[19]);
    assert_obs_eq(actual.1[20], explicit.1[20]);
    assert_obs_eq(actual.1[21], explicit.1[21]);
    assert_obs_eq(actual.1[22], explicit.1[22]);
    assert_obs_eq(actual.1[23], explicit.1[23]);
    assert_obs_eq(actual.1[24], explicit.1[24]);
    assert_obs_eq(actual.1[25], explicit.1[25]);
    assert_obs_eq(actual.1[26], explicit.1[26]);
    assert_obs_eq(actual.1[27], explicit.1[27]);
    assert_obs_eq(actual.1[28], explicit.1[28]);
    assert!(actual.2 == explicit.2);
    assert!(actual.3 == explicit.3);
}

// Focused source cut of the frozen `canonical::Q::from_limbs` check. The
// original expression below is exactly `x.iter().all(|&v| v < P)`; the
// comparison function is exactly the candidate's ordered four predicates.
const Q_P: u32 = 0x7fff_ffff;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q([u32; 4]);

fn q_from_limbs_original(x: [u32; 4]) -> Option<Q> {
    if x.iter().all(|&v| v < Q_P) { Some(Q(x)) } else { None }
}

fn q_from_limbs_candidate(x: [u32; 4]) -> Option<Q> {
    let [a, b, c, d] = x;
    if a < Q_P && b < Q_P && c < Q_P && d < Q_P {
        Some(Q([a, b, c, d]))
    } else {
        None
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(8)]
fn frozen_q_iterator_all_matches_four_ordered_comparisons() {
    let limbs: [u32; 4] = kani::any();
    let original = q_from_limbs_original(limbs);
    let candidate = q_from_limbs_candidate(limbs);
    match (original, candidate) {
        (Some(a), Some(b)) => {
            assert!(a.0[0] == b.0[0]);
            assert!(a.0[1] == b.0[1]);
            assert!(a.0[2] == b.0[2]);
            assert!(a.0[3] == b.0[3]);
        }
        (None, None) => {}
        _ => panic!("constructor results differ"),
    }
}
