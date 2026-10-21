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