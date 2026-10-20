/// A point `(x, y)` on `x^2 + y^2 = 1` over QM31.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SecureCirclePoint {
    pub x: QM31,
    pub y: QM31,
}