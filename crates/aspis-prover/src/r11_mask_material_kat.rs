//! R11 deterministic main-stream control-flow KAT; test-only private access.
use super::*;
use sha2::{Digest, Sha256};
use std::cell::Cell;

thread_local! { static CALLS: Cell<usize> = const { Cell::new(0) }; }
fn hash(parts: &[&[u8]]) -> [u8; 32] {
    CALLS.with(|n| n.set(n.get() + 1));
    let mut h = Sha256::new();
    for part in parts { h.update(part); }
    h.finalize().into()
}
fn hash_values(values: &[QM31]) -> [u8; 32] {
    let mut h = Sha256::new();
    for q in values { for x in [q.c0.a.0, q.c0.b.0, q.c1.a.0, q.c1.b.0] { h.update(x.to_le_bytes()); } }
    h.finalize().into()
}
#[test]
fn r11_main_mask_word_order_matches_python_kat() {
    CALLS.with(|n| n.set(0));
    let context = StateOnlyHidingContext::pool_v1_pair_forest_v1([0x45;32], [0x23;32]);
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let active = pool_v1_pair_forest_copy_active_rows().unwrap();
    let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
    let material = build_mask_material_for_layout(hash, [0xab;32], context, &[0x67;32], &mut nonces, &cells, &active).unwrap();
    assert_eq!(cells.len(), 3803); assert_eq!(active.iter().filter(|v| **v).count(), 214);
    assert_eq!(CALLS.with(Cell::get), 2673);
    assert_eq!(hash_values(&material.g), [127,94,215,199,180,113,209,85,218,146,158,109,9,34,141,78,148,124,154,176,49,215,152,48,71,27,218,3,72,247,71,120]);
    assert_eq!(hash_values(&material.h1_padding), [106,252,122,196,240,202,50,180,211,196,206,245,93,141,211,35,245,42,231,45,121,54,126,200,116,210,252,3,9,29,23,29]);
}
