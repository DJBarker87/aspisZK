// Safe owned reference retaining allocation and fatal-error paths.
pub fn deployed_capacity_reference(n: usize) -> String {
    let mut value = String::new();
    value.reserve_exact(n);
    value
}
