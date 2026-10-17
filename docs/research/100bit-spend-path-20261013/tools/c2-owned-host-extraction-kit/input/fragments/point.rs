/// Coordinates over F, K or E. Construction itself does not assert circle
/// membership or the non-base/distinct hypotheses of the chord theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point<E> {
    pub x: E,
    pub y: E,
}