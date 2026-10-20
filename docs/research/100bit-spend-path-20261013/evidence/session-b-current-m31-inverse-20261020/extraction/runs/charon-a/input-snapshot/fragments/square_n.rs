fn square_n(mut value: M31, count: usize) -> M31 {
    for _ in 0..count {
        value = value.mul(value);
    }
    value
}
