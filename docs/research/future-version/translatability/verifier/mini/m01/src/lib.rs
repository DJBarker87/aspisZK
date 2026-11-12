//! Aspis translatability pass, construct probe m01: which part of `Prepared::new`'s second-challenge step do the
//! tools reject ("Unreachable")? Each function isolates one construct of the pinned text; none is Aspis code.
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

pub struct T { pub state: [u8; 32] }
impl T {
    #[inline(never)]
    pub fn scalar(&mut self, row: u8, bytes: &[u8], flag: bool) -> u32 {
        self.state[0] = self.state[0].wrapping_add(row);
        (bytes.len() as u32).wrapping_add(flag as u32)
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Variant { One, Two }
impl Variant { pub fn folds(self) -> usize { match self { Variant::One => 1, Variant::Two => 2 } } }
pub struct View<'a> { pub variant: Variant, pub folded_root: Option<&'a [u8; 32]>, pub round0: &'a [u8], pub round1: &'a [u8] }

/// The pinned shape: a tuple out of an `if`, a vector and an unwrapped optional reference in one branch.
pub fn pinned_shape(t: &mut T, v: &View<'_>) -> ([u32; 2], u8) {
    let alpha0 = t.scalar(29, v.round0, false);
    let (alpha, row) = if v.variant.folds() == 2 {
        let mut bytes = Vec::with_capacity(32 + 224); bytes.extend_from_slice(v.folded_root.unwrap()); bytes.extend_from_slice(v.round1);
        ([alpha0, t.scalar(30, &bytes, false)], 31)
    } else {
        ([alpha0, 0], 30)
    };
    (alpha, row)
}
/// Only the unwrap of the optional reference read through the shared view.
pub fn unwrap_only(v: &View<'_>) -> u8 { v.folded_root.unwrap()[0] }
/// The optional reference matched in place.
pub fn match_field(v: &View<'_>) -> u8 { match v.folded_root { Some(root) => root[0], None => 0 } }
/// The optional reference through `as_ref`.
pub fn as_ref_unwrap(v: &View<'_>) -> u8 { v.folded_root.as_ref().unwrap()[0] }
/// The optional reference through `expect`-free `if let`.
pub fn if_let_field(v: &View<'_>) -> u8 { if let Some(root) = v.folded_root { root[0] } else { 0 } }
/// The mutable transcript used in one branch only; no option, no vector.
pub fn conditional_mutable_use(t: &mut T, v: &View<'_>) -> u32 { if v.variant.folds() == 2 { t.scalar(30, v.round1, false) } else { 0 } }
/// A vector built and dropped in one branch; no option.
pub fn conditional_vector(t: &mut T, v: &View<'_>) -> u32 {
    if v.variant.folds() == 2 {
        let mut bytes = Vec::with_capacity(32 + 224); bytes.extend_from_slice(v.round0); bytes.extend_from_slice(v.round1);
        t.scalar(30, &bytes, false)
    } else { 0 }
}
/// The tuple out of an `if`; no option, no vector.
pub fn tuple_from_if(t: &mut T, v: &View<'_>) -> ([u32; 2], u8) {
    let alpha0 = t.scalar(29, v.round0, false);
    let (alpha, row) = if v.variant.folds() == 2 { ([alpha0, t.scalar(30, v.round1, false)], 31) } else { ([alpha0, 0], 30) };
    (alpha, row)
}
/// The helper as the second version of patch 1 writes it.
pub fn second_alpha_v2(t: &mut T, v: &View<'_>) -> u32 {
    if v.variant.folds() == 2 {
        let mut bytes = Vec::with_capacity(32 + 224); bytes.extend_from_slice(v.folded_root.unwrap()); bytes.extend_from_slice(v.round1);
        t.scalar(30, &bytes, false)
    } else { 0 }
}
/// The helper with the root passed in by the caller, and the caller's two candidate ways of reading it.
pub fn second_alpha_root(t: &mut T, root: &[u8; 32], round1: &[u8]) -> u32 {
    let mut bytes = Vec::with_capacity(32 + 224); bytes.extend_from_slice(root); bytes.extend_from_slice(round1);
    t.scalar(30, &bytes, false)
}
pub fn caller_unwrap(t: &mut T, v: &View<'_>) -> u32 {
    let two = v.variant.folds() == 2;
    if two { second_alpha_root(t, v.folded_root.unwrap(), v.round1) } else { 0 }
}
pub fn caller_match(t: &mut T, v: &View<'_>) -> u32 {
    if v.variant.folds() == 2 {
        match v.folded_root { Some(root) => second_alpha_root(t, root, v.round1), None => panic!() }
    } else { 0 }
}
pub fn caller_as_ref(t: &mut T, v: &View<'_>) -> u32 {
    if v.variant.folds() == 2 { second_alpha_root(t, v.folded_root.as_ref().unwrap(), v.round1) } else { 0 }
}

// The same constructs with the transcript used again after the `if`, as `Prepared::new` does (rows 31/32 and the
// final state follow the second challenge).
/// First reshaping of patch 1, with a continuation.
pub fn first_reshaping_with_continuation(t: &mut T, v: &View<'_>) -> ([u32; 2], u32, u8) {
    let alpha0 = t.scalar(29, v.round0, false);
    let two = v.variant.folds() == 2;
    let alpha1 = if two { second_alpha_root(t, v.folded_root.unwrap(), v.round1) } else { 0 };
    let alpha = [alpha0, alpha1];
    let row: u8 = if two { 31 } else { 30 };
    let q = t.scalar(row, v.round0, true);
    (alpha, q, t.state[0])
}
/// Second reshaping of patch 1 (the helper takes the view), with a continuation.
pub fn second_reshaping_with_continuation(t: &mut T, v: &View<'_>) -> ([u32; 2], u32, u8) {
    let alpha0 = t.scalar(29, v.round0, false);
    let alpha = [alpha0, second_alpha_v2(t, v)];
    let row: u8 = if v.variant.folds() == 2 { 31 } else { 30 };
    let q = t.scalar(row, v.round0, true);
    (alpha, q, t.state[0])
}
/// The conditional mutable use alone, with a continuation; no option, no vector.
pub fn conditional_mutable_use_with_continuation(t: &mut T, v: &View<'_>) -> (u32, u32, u8) {
    let a = if v.variant.folds() == 2 { t.scalar(30, v.round1, false) } else { 0 };
    let q = t.scalar(31, v.round0, true);
    (a, q, t.state[0])
}
/// The unwrap alone in one branch, with a continuation; the transcript is not touched in the branch.
pub fn conditional_unwrap_with_continuation(t: &mut T, v: &View<'_>) -> (u8, u32, u8) {
    let a = if v.variant.folds() == 2 { v.folded_root.unwrap()[0] } else { 0 };
    let q = t.scalar(31, v.round0, true);
    (a, q, t.state[0])
}
/// The optional reference matched in place in one branch, with a continuation.
pub fn conditional_match_with_continuation(t: &mut T, v: &View<'_>) -> (u32, u32, u8) {
    let a = if v.variant.folds() == 2 {
        match v.folded_root { Some(root) => second_alpha_root(t, root, v.round1), None => panic!() }
    } else { 0 };
    let q = t.scalar(31, v.round0, true);
    (a, q, t.state[0])
}
/// The pinned shape with an owned transcript (as in `Prepared::new`, where the transcript is a local) and a continuation.
pub fn pinned_shape_owned(v: &View<'_>) -> ([u32; 2], u32, [u8; 32]) {
    let mut t = T { state: [0; 32] };
    let alpha0 = t.scalar(29, v.round0, false);
    let (alpha, row) = if v.variant.folds() == 2 {
        let mut bytes = Vec::with_capacity(32 + 224); bytes.extend_from_slice(v.folded_root.unwrap()); bytes.extend_from_slice(v.round1);
        ([alpha0, t.scalar(30, &bytes, false)], 31)
    } else {
        ([alpha0, 0], 30)
    };
    let q = t.scalar(row, v.round0, true);
    (alpha, q, t.state)
}
/// Second reshaping with an owned transcript and a continuation.
pub fn second_reshaping_owned(v: &View<'_>) -> ([u32; 2], u32, [u8; 32]) {
    let mut t = T { state: [0; 32] };
    let alpha0 = t.scalar(29, v.round0, false);
    let alpha = [alpha0, second_alpha_v2(&mut t, v)];
    let row: u8 = if v.variant.folds() == 2 { 31 } else { 30 };
    let q = t.scalar(row, v.round0, true);
    (alpha, q, t.state)
}
