//! Differential test for the P6 stateful `array::from_fn` success model.
//! The explicit loop is the harness model: call at indices 0..N, thread
//! captured state, then materialize the same fixed array.

fn model_from_fn<T, const N: usize, F>(mut callback: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    let mut values = Vec::with_capacity(N);
    for index in 0..N {
        values.push(callback(index));
    }
    values.try_into().ok().expect("exactly N values were appended")
}

fn compare<const N: usize>(seed: u64, multiplier: u64) {
    let mut std_state = seed;
    let mut model_state = seed;
    let mut std_calls = Vec::new();
    let mut model_calls = Vec::new();

    let actual: [u64; N] = std::array::from_fn(|i| {
        std_calls.push(i);
        let out = std_state.wrapping_mul(multiplier).wrapping_add(i as u64);
        std_state = out.rotate_left((i % 63) as u32) ^ (i as u64 + 1);
        out
    });
    let modeled: [u64; N] = model_from_fn(|i| {
        model_calls.push(i);
        let out = model_state.wrapping_mul(multiplier).wrapping_add(i as u64);
        model_state = out.rotate_left((i % 63) as u32) ^ (i as u64 + 1);
        out
    });

    assert_eq!(modeled, actual, "array values, N={N}");
    assert_eq!(model_calls, std_calls, "call order, N={N}");
    assert_eq!(model_state, std_state, "final capture state, N={N}");
    assert_eq!(std_calls, (0..N).collect::<Vec<_>>());
}

#[test]
fn differential_stateful_from_fn_admitted_lengths() {
    for (seed, multiplier) in [(0, 0), (1, 1), (7, 13), (u64::MAX, 0x9e37_79b9)] {
        compare::<0>(seed, multiplier);
        compare::<1>(seed, multiplier);
        compare::<4>(seed, multiplier);
        compare::<8>(seed, multiplier);
        compare::<16>(seed, multiplier);
        compare::<29>(seed, multiplier);
    }
}
