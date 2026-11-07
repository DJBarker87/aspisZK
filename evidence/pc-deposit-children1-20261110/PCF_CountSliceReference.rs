// Borrow-minimal typed slice view of frozen pair_forest.rs:371-380.
// Payload T is never inspected; exact full reply arms are 0/1/2.
pub fn count_reference<T>(accounts: &[T], expected: usize) -> u8 {
    if accounts.len() != expected {
        return if accounts.len() < expected { 1 } else { 2 };
    }
    0
}
