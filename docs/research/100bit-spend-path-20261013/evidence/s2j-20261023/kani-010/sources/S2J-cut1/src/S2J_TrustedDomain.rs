#![cfg(kani)]
//! Executable route-B SPECIFICATION, not SDK implementation verification.
//! Cell/token/owner identities are abstract, never address or layout assertions.
//! Bounded projection of S2TrustedSdkBorrow: three cells/handles, three local tokens,
//! two payload positions; full signed i64 external counters, arbitrary descriptors
//! and ambient data. Later caller users must check their capacities/admission and
//! supply typed per-call/implicit-cleanup simulation to the unchanged source.
//! `step` has a checked contract for `stub_verified`; no foreign guard is havoced.

pub const CELLS: usize = 3;
pub const TOKENS: usize = 3;
pub const WIDTH: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, kani::Arbitrary)]
pub struct Descriptor { pub base: u64, pub len: usize, pub provenance: u64 }
#[derive(Clone, Copy, Debug, Eq, kani::Arbitrary)]
pub struct Payload { pub descriptor: Descriptor, pub contents: [u8; WIDTH] }
#[derive(Clone, Copy, Debug, PartialEq, Eq, kani::Arbitrary)]
pub struct Guard { pub cell: usize, pub owner: u8, pub exclusive: bool, pub descriptor: Descriptor }
#[derive(Clone, Copy, Debug, Eq, kani::Arbitrary)]
pub struct State {
    pub accounts: [usize; CELLS],
    pub lamports: [u64; CELLS],
    pub owner_live: [bool; CELLS],
    pub allocated: [bool; CELLS],
    pub payload: [Payload; CELLS],
    pub counter: [i64; CELLS],
    pub external: [i64; CELLS],
    pub guards: [Option<Guard>; TOKENS],
    pub ambient: [u64; 4],
}
// Explicit bounded comparisons avoid std's bytewise memcmp loop, whose trip
// count is struct byte size rather than the logical cell/token loop bound.
fn array_eq<T: PartialEq, const N: usize>(a: &[T; N], b: &[T; N]) -> bool {
    for i in 0..N { if a[i] != b[i] { return false; } }
    true
}
impl PartialEq for Payload {
    fn eq(&self, other: &Self) -> bool { self.descriptor == other.descriptor && array_eq(&self.contents,&other.contents) }
}
impl PartialEq for State {
    fn eq(&self, o: &Self) -> bool {
        array_eq(&self.accounts,&o.accounts) && array_eq(&self.lamports,&o.lamports) &&
        array_eq(&self.owner_live,&o.owner_live) && array_eq(&self.allocated,&o.allocated) &&
        array_eq(&self.payload,&o.payload) && array_eq(&self.counter,&o.counter) &&
        array_eq(&self.external,&o.external) && array_eq(&self.guards,&o.guards) && array_eq(&self.ambient,&o.ambient)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, kani::Arbitrary)]
pub enum Op {
    Shared { account: usize, token: usize, owner: u8 },
    Exclusive { account: usize, token: usize, owner: u8 },
    Deref { token: usize },
    Write { token: usize, index: usize, value: u8 },
    Move { token: usize, destination: u8 },
    Drop { token: usize },
    ErrorMoveDrop,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, kani::Arbitrary)]
pub enum Reply { Guard(usize), BorrowFailed, Payload(Payload), Unit }

pub fn valid(s: &State) -> bool {
    for a in 0..CELLS {
        if s.accounts[a] >= CELLS { return false; }
        if s.owner_live[a] && (!s.allocated[s.accounts[a]] || s.accounts[a] as u64 == s.lamports[a]) { return false; }
        if s.payload[a].descriptor.len > WIDTH { return false; }
    }
    for t in 0..TOKENS {
        if let Some(g) = s.guards[t] {
            if g.cell >= CELLS || !s.allocated[g.cell] || g.descriptor != s.payload[g.cell].descriptor { return false; }
            for u in 0..t {
                if let Some(h) = s.guards[u] { if h.owner == g.owner { return false; } }
            }
        }
    }
    for c in 0..CELLS {
        let mut shared = 0i128;
        let mut exclusive = 0i128;
        for t in 0..TOKENS {
            if let Some(g) = s.guards[t] { if g.cell == c {
                if g.exclusive { exclusive += 1; } else { shared += 1; }
            }}
        }
        if s.counter[c] as i128 != s.external[c] as i128 + shared - exclusive { return false; }
        if exclusive > 0 && (s.external[c] != 0 || shared != 0 || exclusive != 1) { return false; }
        if s.external[c] < 0 && (shared != 0 || exclusive != 0) { return false; }
    }
    true
}
