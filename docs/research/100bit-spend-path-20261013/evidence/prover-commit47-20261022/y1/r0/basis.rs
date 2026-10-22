use super::CodeField;
pub(crate) fn double<E: CodeField>(x: E) -> E {
    let square = x.mul(x);
    square.add(square).sub(E::ONE)
}
pub(crate) fn values<E: CodeField, const N: usize>(x: E) -> [E; N] {
    let mut out = [E::ONE; N];
    let mut width = 1;
    let mut factor = x;
    while width < N {
        for j in 0..width.min(N - width) {
            out[width + j] = out[j].mul(factor);
        }
        width *= 2;
        factor = double(factor);
    }
    out
}
