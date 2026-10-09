//! Native-only nested-operation accounting. Inclusive counts audit the tower;
//! exclusive counts price only outermost primitives, preventing double charging.
//! Reset/read on the single verifier thread; absent unless explicitly enabled.
#![allow(unexpected_cfgs)]
#[cfg(target_os = "solana")]
compile_error!("r0-op-count is a native-only diagnostic");
extern crate std;
use std::cell::RefCell;
#[derive(Clone, Copy, Debug)]
#[repr(usize)]
pub enum Op {
    EAdd,
    ESub,
    ENeg,
    EMul,
    ESquare,
    EMulK,
    EMulF,
    EInv,
    EInvGeneric,
    KAdd,
    KSub,
    KNeg,
    KMul,
    KSquare,
    KMulF,
    KMulC,
    KInv,
    KInvGeneric,
    FAdd,
    FSub,
    FNeg,
    FMul,
    FInv,
    FInvGeneric,
    FHalf,
    FMulPow2,
    ShaCompression,
    ShaCall,
}
pub const N: usize = 28;
pub const NAMES: [&str; N] = [
    "EAdd",
    "ESub",
    "ENeg",
    "EMul",
    "ESquare",
    "EMulK",
    "EMulF",
    "EInv",
    "EInvGeneric",
    "KAdd",
    "KSub",
    "KNeg",
    "KMul",
    "KSquare",
    "KMulF",
    "KMulC",
    "KInv",
    "KInvGeneric",
    "FAdd",
    "FSub",
    "FNeg",
    "FMul",
    "FInv",
    "FInvGeneric",
    "FHalf",
    "FMulPow2",
    "ShaCompression",
    "ShaCall",
];
#[derive(Clone)]
struct Counts {
    depth: usize,
    inclusive: [u64; N],
    exclusive: [u64; N],
}
std::thread_local! { static COUNTS: RefCell<Counts> = const { RefCell::new(Counts {depth:0,inclusive:[0;N],exclusive:[0;N]}) }; }
pub struct Guard;
pub fn enter(op: Op) -> Guard {
    COUNTS.with(|c| {
        let mut c = c.borrow_mut();
        c.inclusive[op as usize] += 1;
        if c.depth == 0 {
            c.exclusive[op as usize] += 1;
        }
        c.depth += 1;
    });
    Guard
}
impl Drop for Guard {
    fn drop(&mut self) {
        COUNTS.with(|c| c.borrow_mut().depth -= 1);
    }
}
pub fn take() -> ([u64; N], [u64; N]) {
    COUNTS.with(|c| {
        let mut c = c.borrow_mut();
        assert_eq!(c.depth, 0);
        let out = (c.inclusive, c.exclusive);
        c.inclusive.fill(0);
        c.exclusive.fill(0);
        out
    })
}
pub fn hash(parts: &[&[u8]]) {
    let n = parts.iter().map(|x| x.len()).sum::<usize>();
    COUNTS.with(|c| {
        let mut c = c.borrow_mut();
        for (op, v) in [
            (Op::ShaCompression, ((n + 9 + 63) / 64) as u64),
            (Op::ShaCall, 1),
        ] {
            c.inclusive[op as usize] += v;
            c.exclusive[op as usize] += v;
        }
    });
}
