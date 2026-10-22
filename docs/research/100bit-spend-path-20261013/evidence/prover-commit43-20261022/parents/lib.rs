//! Native-source diagnostic, not an owned reference or a trusted contract.
use std::collections::{BTreeMap,BTreeSet};
pub fn parents(level:&BTreeMap<usize,[u8;32]>)->BTreeSet<usize> {
    let parents:BTreeSet<usize>=level.keys().map(|i|i/2).collect();
    parents
}
