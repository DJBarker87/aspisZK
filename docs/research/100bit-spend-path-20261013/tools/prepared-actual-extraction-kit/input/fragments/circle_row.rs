/// Selects the existing row fallback: parameter u for row 25, 1+u for 26.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleRow {
    First,
    Second,
}