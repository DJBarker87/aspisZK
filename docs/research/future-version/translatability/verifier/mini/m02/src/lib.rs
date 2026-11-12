//! Aspis translatability pass, construct probe m02: which loop forms of `canonical_scan` and of the backward pass of
//! `QueryGeometry::for_range` do the tools translate? Stand-in types; none of this is Aspis code.
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error { Parse, Query }
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct M31(pub u32);
pub const P: u32 = 0x7fff_ffff;
impl M31 {
    pub const ZERO: M31 = M31(0);
    pub const ONE: M31 = M31(1);
    #[inline(always)]
    pub fn from_le_bytes(b: [u8; 4]) -> Option<M31> { let x = u32::from_le_bytes(b); if x < P { Some(M31(x)) } else { None } }
    #[inline(never)]
    pub fn mul(self, o: M31) -> M31 { M31(((self.0 as u64 * o.0 as u64) % (P as u64)) as u32) }
    #[inline(never)]
    pub fn inv(self) -> M31 { self }
}
#[derive(Clone, Copy)]
pub struct K(pub [u32; 4]);
impl K {
    #[inline(never)]
    pub fn from_le_bytes(b: &[u8]) -> Option<K> { if b.len() == 16 && b[3] < 0x80 { Some(K([b[0] as u32; 4])) } else { None } }
}
#[inline(never)]
pub fn echeck(b: &[u8], k: bool) -> Result<(), Error> { if b.len() % 32 == 0 && !k { Ok(()) } else { Err(Error::Parse) } }
pub const OPENING: usize = 832;
#[inline(always)]
fn opening(proof: &[u8], i: usize) -> &[u8] { let at = 64 + i * OPENING; &proof[at..at + OPENING] }

// ---- canonical_scan forms ----
/// The pinned nest.
pub fn scan_pinned(proof: &[u8]) -> Result<(), Error> {
    echeck(&proof[0..32], false)?;
    for i in 0..22 {
        let q = opening(proof, i);
        for s in 0..4 {
            for l in 0..26 {
                M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
            }
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            for l in 0..2 {
                K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
            }
        }
        echeck(&q[672..800], false)?;
    }
    Ok(())
}
pub mod split {
    use super::*;
    fn scan_slot_base(q: &[u8], s: usize) -> Result<(), Error> {
        for l in 0..26 { M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?; }
        Ok(())
    }
    fn scan_slot_extension(q: &[u8], s: usize) -> Result<(), Error> {
        for l in 0..2 { K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?; }
        Ok(())
    }
    fn scan_opening(q: &[u8]) -> Result<(), Error> {
        for s in 0..4 {
            scan_slot_base(q, s)?;
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            scan_slot_extension(q, s)?;
        }
        echeck(&q[672..800], false)
    }
    pub fn scan(proof: &[u8]) -> Result<(), Error> {
        echeck(&proof[0..32], false)?;
        for i in 0..22 { scan_opening(opening(proof, i))?; }
        Ok(())
    }
}
pub mod subslice {
    use super::*;
    fn scan_slot_base(slot: &[u8]) -> Result<(), Error> {
        for l in 0..26 { M31::from_le_bytes(slot[l * 4..l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?; }
        Ok(())
    }
    fn scan_slot_extension(pair: &[u8]) -> Result<(), Error> {
        for l in 0..2 { K::from_le_bytes(&pair[l * 16..l * 16 + 16]).ok_or(Error::Parse)?; }
        Ok(())
    }
    fn scan_opening(q: &[u8]) -> Result<(), Error> {
        for s in 0..4 {
            scan_slot_base(&q[s * 120..s * 120 + 104])?;
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            scan_slot_extension(&q[480 + s * 32..480 + s * 32 + 32])?;
        }
        echeck(&q[672..800], false)
    }
    pub fn scan(proof: &[u8]) -> Result<(), Error> {
        echeck(&proof[0..32], false)?;
        for i in 0..22 { scan_opening(opening(proof, i))?; }
        Ok(())
    }
}
pub mod unrolled {
    use super::*;
    fn scan_slot(q: &[u8], s: usize) -> Result<(), Error> {
        for l in 0..26 { M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?; }
        K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
        K::from_le_bytes(&q[480 + s * 32..480 + s * 32 + 16]).ok_or(Error::Parse)?;
        K::from_le_bytes(&q[480 + s * 32 + 16..480 + s * 32 + 32]).ok_or(Error::Parse)?;
        Ok(())
    }
    fn scan_opening(q: &[u8]) -> Result<(), Error> {
        scan_slot(q, 0)?; scan_slot(q, 1)?; scan_slot(q, 2)?; scan_slot(q, 3)?;
        echeck(&q[672..800], false)
    }
    pub fn scan(proof: &[u8]) -> Result<(), Error> {
        echeck(&proof[0..32], false)?;
        for i in 0..22 { scan_opening(opening(proof, i))?; }
        Ok(())
    }
}
pub mod subslice_unrolled {
    use super::*;
    fn scan_slot(slot: &[u8], pair: &[u8]) -> Result<(), Error> {
        for l in 0..26 { M31::from_le_bytes(slot[l * 4..l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?; }
        K::from_le_bytes(&slot[104..120]).ok_or(Error::Parse)?;
        K::from_le_bytes(&pair[..16]).ok_or(Error::Parse)?;
        K::from_le_bytes(&pair[16..32]).ok_or(Error::Parse)?;
        Ok(())
    }
    fn scan_opening(q: &[u8]) -> Result<(), Error> {
        scan_slot(&q[0..120], &q[480..512])?;
        scan_slot(&q[120..240], &q[512..544])?;
        scan_slot(&q[240..360], &q[544..576])?;
        scan_slot(&q[360..480], &q[576..608])?;
        echeck(&q[672..800], false)
    }
    pub fn scan(proof: &[u8]) -> Result<(), Error> {
        echeck(&proof[0..32], false)?;
        for i in 0..22 { scan_opening(opening(proof, i))?; }
        Ok(())
    }
}
pub mod boolean {
    use super::*;
    fn scan_slot_base(q: &[u8], s: usize) -> bool {
        for l in 0..26 { if M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).is_none() { return false; } }
        true
    }
    fn scan_slot_extension(q: &[u8], s: usize) -> bool {
        for l in 0..2 { if K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).is_none() { return false; } }
        true
    }
    fn scan_opening(q: &[u8]) -> Result<(), Error> {
        for s in 0..4 {
            if !scan_slot_base(q, s) { return Err(Error::Parse); }
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            if !scan_slot_extension(q, s) { return Err(Error::Parse); }
        }
        echeck(&q[672..800], false)
    }
    pub fn scan(proof: &[u8]) -> Result<(), Error> {
        echeck(&proof[0..32], false)?;
        for i in 0..22 { scan_opening(opening(proof, i))?; }
        Ok(())
    }
}
/// The nest with a flag in place of the early return.
pub fn scan_flag(proof: &[u8]) -> Result<(), Error> {
    echeck(&proof[0..32], false)?;
    let mut canonical = true;
    for i in 0..22 {
        let q = opening(proof, i);
        for s in 0..4 {
            for l in 0..26 {
                canonical &= M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).is_some();
            }
            canonical &= K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).is_some();
            for l in 0..2 {
                canonical &= K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).is_some();
            }
        }
        canonical &= echeck(&q[672..800], false).is_ok();
    }
    if canonical { Ok(()) } else { Err(Error::Parse) }
}

// ---- the backward pass of the batch inversion ----
fn prefix_products(flat: &[M31]) -> (Vec<M31>, M31) {
    let mut prefixes = Vec::with_capacity(flat.len());
    let mut product = M31::ONE;
    let mut index = 0;
    while index < flat.len() { let value = flat[index]; prefixes.push(product); product = product.mul(value); index += 1; }
    (prefixes, product)
}
/// A helper of its own, counting loop (the form patch 2 now has).
pub fn suffix_inverses_while(flat: &[M31], prefixes: &[M31], product: M31) -> Vec<M31> {
    let mut suffix_inverse = product.inv();
    let mut flat_inverse = Vec::with_capacity(flat.len());
    flat_inverse.resize(flat.len(), M31::ZERO);
    let mut i = flat.len();
    while i > 0 {
        i -= 1;
        flat_inverse[i] = suffix_inverse.mul(prefixes[i]);
        suffix_inverse = suffix_inverse.mul(flat[i]);
    }
    flat_inverse
}
/// A helper of its own, the pinned reversed range.
pub fn suffix_inverses_rev(flat: &[M31], prefixes: &[M31], product: M31) -> Vec<M31> {
    let mut suffix_inverse = product.inv();
    let mut flat_inverse = Vec::with_capacity(flat.len());
    flat_inverse.resize(flat.len(), M31::ZERO);
    for i in (0..flat.len()).rev() {
        flat_inverse[i] = suffix_inverse.mul(prefixes[i]);
        suffix_inverse = suffix_inverse.mul(flat[i]);
    }
    flat_inverse
}
/// A helper of its own, forward counter with the mirrored position.
pub fn suffix_inverses_mirrored(flat: &[M31], prefixes: &[M31], product: M31) -> Vec<M31> {
    let mut suffix_inverse = product.inv();
    let n = flat.len();
    let mut flat_inverse = Vec::with_capacity(n);
    flat_inverse.resize(n, M31::ZERO);
    let mut k = 0;
    while k < n {
        let i = n - 1 - k;
        flat_inverse[i] = suffix_inverse.mul(prefixes[i]);
        suffix_inverse = suffix_inverse.mul(flat[i]);
        k += 1;
    }
    flat_inverse
}
/// The shape of `for_range` with the helper: first loop with early returns, then the helpers, then the collect.
pub fn for_range_with_helper(queries: &[u32; 22], start: usize, end: usize) -> Result<Vec<[M31; 5]>, Error> {
    if start > end || end > queries.len() { return Err(Error::Query); }
    let mut flat = Vec::with_capacity((end - start) * 5);
    for &query in &queries[start..end] {
        let x = M31::from_le_bytes(query.to_le_bytes()).ok_or(Error::Query)?;
        let values = [x, x, x, x, x.mul(x)];
        if values.iter().any(|v| *v == M31::ZERO) { return Err(Error::Query); }
        flat.extend_from_slice(&values);
    }
    if flat.is_empty() { return Ok(Vec::new()); }
    let (prefixes, product) = prefix_products(&flat);
    let flat_inverse = suffix_inverses_while(&flat, &prefixes, product);
    let inverses = (0..end - start).map(|i| core::array::from_fn(|j| flat_inverse[5 * i + j])).collect();
    Ok(inverses)
}
/// The shape of `for_range` with the counting loop inside it (the first batch's form; the tools rejected it).
pub fn for_range_inline(queries: &[u32; 22], start: usize, end: usize) -> Result<Vec<[M31; 5]>, Error> {
    if start > end || end > queries.len() { return Err(Error::Query); }
    let mut flat = Vec::with_capacity((end - start) * 5);
    for &query in &queries[start..end] {
        let x = M31::from_le_bytes(query.to_le_bytes()).ok_or(Error::Query)?;
        let values = [x, x, x, x, x.mul(x)];
        if values.iter().any(|v| *v == M31::ZERO) { return Err(Error::Query); }
        flat.extend_from_slice(&values);
    }
    if flat.is_empty() { return Ok(Vec::new()); }
    let (prefixes, product) = prefix_products(&flat);
    let mut suffix_inverse = product.inv();
    let mut flat_inverse = Vec::with_capacity(flat.len());
    flat_inverse.resize(flat.len(), M31::ZERO);
    let mut i = flat.len();
    while i > 0 {
        i -= 1;
        flat_inverse[i] = suffix_inverse.mul(prefixes[i]);
        suffix_inverse = suffix_inverse.mul(flat[i]);
    }
    let inverses = (0..end - start).map(|i| core::array::from_fn(|j| flat_inverse[5 * i + j])).collect();
    Ok(inverses)
}

// ---- adapter shapes ----
pub struct Acc { pub key: [u8; 32], pub owner: [u8; 32] }
impl Acc { fn key(&self) -> &[u8; 32] { &self.key } }
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PErr { InvalidArgument, InvalidAccountData }
/// The pinned pairwise comparison (nested loops with a return, over an array of references).
pub fn distinct_pinned<const N: usize>(accounts: &[&Acc; N]) -> Result<(), PErr> {
    let mut index = 0;
    while index < N {
        let mut previous = 0;
        while previous < index {
            if accounts[previous].key() == accounts[index].key() { return Err(PErr::InvalidArgument); }
            previous += 1;
        }
        index += 1;
    }
    Ok(())
}
/// The first batch's flag form (the tools rejected it: nested borrows in the loop).
pub fn distinct_flag<const N: usize>(accounts: &[&Acc; N]) -> Result<(), PErr> {
    let mut distinct = true;
    let mut index = 0;
    while index < N {
        let mut previous = 0;
        while previous < index {
            if accounts[previous].key() == accounts[index].key() { distinct = false; }
            previous += 1;
        }
        index += 1;
    }
    if distinct { Ok(()) } else { Err(PErr::InvalidArgument) }
}
/// The comparisons written out for three accounts (the seven-account form is the same shape, 21 lines).
pub fn distinct_three(a: &[&Acc; 3]) -> Result<(), PErr> {
    if a[0].key() == a[1].key() { return Err(PErr::InvalidArgument); }
    if a[0].key() == a[2].key() { return Err(PErr::InvalidArgument); }
    if a[1].key() == a[2].key() { return Err(PErr::InvalidArgument); }
    Ok(())
}
/// Keys by value, flag form, nested loops.
pub fn distinct_keys_flag<const N: usize>(keys: &[[u8; 32]; N]) -> Result<(), PErr> {
    let mut distinct = true;
    let mut index = 0;
    while index < N {
        let mut previous = 0;
        while previous < index {
            if keys[previous] == keys[index] { distinct = false; }
            previous += 1;
        }
        index += 1;
    }
    if distinct { Ok(()) } else { Err(PErr::InvalidArgument) }
}
/// A caller that builds the array of references and one that builds the array of keys.
pub fn caller_refs(x: &[Acc]) -> Result<(), PErr> {
    if x.len() != 3 { return Err(PErr::InvalidArgument); }
    let a = &x[0]; let b = &x[1]; let c = &x[2];
    distinct_three(&[a, b, c])
}
pub fn caller_keys(x: &[Acc]) -> Result<(), PErr> {
    if x.len() != 3 { return Err(PErr::InvalidArgument); }
    let a = &x[0]; let b = &x[1]; let c = &x[2];
    distinct_keys_flag(&[*a.key(), *b.key(), *c.key()])
}

pub static EMPTY: [[M31; 8]; 21] = [[M31(7); 8]; 21];
#[inline(never)]
fn decode_digest(b: [u8; 32]) -> Result<[M31; 8], Error> { if b[3] < 0x80 { Ok([M31(b[0] as u32); 8]) } else { Err(Error::Parse) } }
/// The first batch's frontier loop (the tools rejected it at the `if`).
pub fn frontier_first(tree: &[u8], next: u64) -> Result<[[M31; 8]; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        let start = 48 + 32 * level;
        match decode_digest(tree[start..start + 32].try_into().unwrap()) {
            Ok(node) => {
                if (next >> level) & 1 == 0 && node != EMPTY[level] { ok = false; }
                frontier[level] = node;
            }
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
/// One node, both checks in the helper, every branch a tail.
fn node_all_tails(tree: &[u8], level: usize, next: u64) -> Result<[M31; 8], PErr> {
    let start = 48 + 32 * level;
    let node = decode_digest(tree[start..start + 32].try_into().map_err(|_| PErr::InvalidAccountData)?).map_err(|_| PErr::InvalidAccountData)?;
    if (next >> level) & 1 == 0 {
        if node != EMPTY[level] { Err(PErr::InvalidAccountData) } else { Ok(node) }
    } else {
        Ok(node)
    }
}
pub fn frontier_all_tails(tree: &[u8], next: u64) -> Result<[[M31; 8]; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        match node_all_tails(tree, level, next) {
            Ok(node) => frontier[level] = node,
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
/// One node, both checks in the helper, `&&` and an early return.
fn node_and(tree: &[u8], level: usize, next: u64) -> Result<[M31; 8], PErr> {
    let start = 48 + 32 * level;
    let node = decode_digest(tree[start..start + 32].try_into().map_err(|_| PErr::InvalidAccountData)?).map_err(|_| PErr::InvalidAccountData)?;
    if (next >> level) & 1 == 0 && node != EMPTY[level] {
        return Err(PErr::InvalidAccountData);
    }
    Ok(node)
}
pub fn frontier_and(tree: &[u8], next: u64) -> Result<[[M31; 8]; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        match node_and(tree, level, next) {
            Ok(node) => frontier[level] = node,
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
/// The comparison made on every level, before the test of the index bit.
pub fn frontier_always(tree: &[u8], next: u64) -> Result<[[M31; 8]; 20], PErr> {
    let mut frontier = [[M31::ZERO; 8]; 20];
    let mut ok = true;
    let mut level = 0;
    while level < 20 {
        let start = 48 + 32 * level;
        match decode_digest(tree[start..start + 32].try_into().unwrap()) {
            Ok(node) => {
                let empty = node == EMPTY[level];
                if (next >> level) & 1 == 0 && !empty { ok = false; }
                frontier[level] = node;
            }
            Err(_) => ok = false,
        }
        level += 1;
    }
    if !ok { return Err(PErr::InvalidAccountData); }
    Ok(frontier)
}
