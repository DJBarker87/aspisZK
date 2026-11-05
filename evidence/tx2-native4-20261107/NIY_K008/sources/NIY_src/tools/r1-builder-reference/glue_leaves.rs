//! Per-function Kani checks against the R1Z record/glue formulas.
//! Included only through the existing cfg(kani) proof module. No stubs.
use super::super::*;
fn words() -> [u32; 8] { [kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any()] }
fn witness() -> RW {
    RW { input_value: kani::any(), output_value: kani::any(), change_value: kani::any(),
        sk: words(), salt: words(), bits: [0;24], sibs: [[0;8];24],
        pair_first: words(), pair_occupied: kani::any(), pair_second: words(), pair_inverse: kani::any(),
        recipient_owner: words(), recipient_salt: words(), change_owner: words(), change_salt: words() }
}
fn public() -> RP {
    RP { transfer: kani::any(), asset: kani::any(), next_pair_index: kani::any(),
         frontier: [[0;8];20], empty: [[0;8];20] }
}

#[kani::proof]
#[kani::unwind(9)]
fn glue_note_c2() {
    let salt = words(); let value = kani::any(); let asset = kani::any();
    let actual = note_c2r(value, asset, &salt);
    let expected = [value, asset, salt[0], salt[1], salt[2], salt[3], salt[4], salt[5]];
    for i in 0..8 { assert_eq!(actual[i], expected[i]); }
}
#[kani::proof]
#[kani::unwind(9)]
fn glue_note_c3() {
    let salt = words();
    let actual = note_c3r(&salt); let expected = [salt[6], salt[7], 0, 0, 0, 0, 0, 0];
    for i in 0..8 { assert_eq!(actual[i], expected[i]); }
}
#[kani::proof]
#[kani::unwind(9)]
fn glue_ordered() {
    let cur = words(); let sib = words(); let b: bool = kani::any();
    let expected = if b { (sib, cur) } else { (cur, sib) };
    let actual = ordered_r(cur, sib, b);
    for i in 0..8 { assert_eq!(actual.0[i], expected.0[i]); assert_eq!(actual.1[i], expected.1[i]); }
}
#[kani::proof]
fn glue_bit() {
    let mut w = witness(); let n: usize = kani::any(); kani::assume(n < 24);
    let x: u32 = kani::any(); w.bits[n] = x;
    assert_eq!(bit_b(&w, n), x != 0);
}
#[kani::proof]
fn glue_append_bit() {
    let mut p = public(); let n: usize = kani::any(); kani::assume(n < 20);
    p.next_pair_index = kani::any();
    assert_eq!(app_bit_r(&p, n), ((p.next_pair_index / (1u64 << n)) % 2) == 1);
}
#[kani::proof]
#[kani::unwind(9)]
fn glue_append_sibling() {
    let mut p = public(); let n: usize = kani::any(); kani::assume(n < 20);
    let f = words(); let e = words(); p.frontier[n] = f; p.empty[n] = e;
    let b = ((p.next_pair_index / (1u64 << n)) % 2) == 1;
    let actual = app_sib_r(&p, n); let expected = if b { f } else { e };
    for i in 0..8 { assert_eq!(actual[i], expected[i]); }
}
#[kani::proof]
fn glue_node_kind() {
    let h: usize = kani::any();
    assert_eq!(node_kind(h), (4 <= h && h < 25) || (33 <= h && h < 57));
}
#[kani::proof]
fn glue_zero_kind() {
    let p = public(); let h: usize = kani::any();
    assert_eq!(zero_kind(&p, h), !p.transfer && 27 <= h && h < 30);
}
#[kani::proof]
fn glue_late_row() {
    let k: usize = kani::any();
    assert_eq!(late_row(k), 544 <= k % 1024 && k % 1024 < 864);
}
#[kani::proof]
fn glue_chunk_length() {
    let h: usize = kani::any();
    assert_eq!(sclen(h), if h == 3 || h == 29 || h == 32 { 2 } else { 8 });
}
#[kani::proof]
#[kani::unwind(9)]
fn glue_input_occupancy() {
    let mut w = witness(); w.bits[0] = kani::any();
    let r = in_rec(&w);
    assert_eq!(r.occupied, w.pair_occupied); assert_eq!(r.inverse, w.pair_inverse);
    for i in 0..8 { assert_eq!(r.commitment[i], w.pair_second[i]); } assert_eq!(r.selected, w.bits[0]);
    assert!(r.has_selected);
}

#[kani::proof]
#[kani::unwind(9)]
fn glue_digest_projection() {
    let s: [u32;16] = [kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any(), kani::any()];
    let d=digest8(s);
    for i in 0..8 { assert_eq!(d[i],s[i]); }
}

// The actual std adapter used by digest8/noteC2R/noteC3R. Arbitrary shared
// return table, ordered callback indices, every result word, exact call count.
#[kani::proof]
#[kani::unwind(9)]
fn glue_from_fn8_contract() {
    let table = words(); let mut calls=0usize;
    let out: [u32;8] = core::array::from_fn(|i| {
        assert_eq!(i,calls); calls+=1; table[i]
    });
    assert_eq!(calls,8);
    for i in 0..8 { assert_eq!(out[i],table[i]); }
}
