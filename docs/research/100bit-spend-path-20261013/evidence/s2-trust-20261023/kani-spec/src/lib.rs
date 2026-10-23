#![cfg(kani)]
//! Executable route-B SPECIFICATION, not SDK implementation verification.
//! Cell/token/owner identities are abstract, never address or layout assertions.
//! Bounded projection of S2TrustedSdkBorrow: two cells/handles, three local tokens,
//! two payload positions; full signed i64 external counters, arbitrary descriptors
//! and ambient data. Later caller users must check their capacities/admission and
//! supply typed per-call/implicit-cleanup simulation to the unchanged source.
//! `step` has a checked contract for `stub_verified`; no foreign guard is havoced.

pub const CELLS: usize = 2;
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
fn vacant(s: &State, owner: u8) -> bool {
    for g in s.guards { if let Some(g) = g { if g.owner == owner { return false; } } }
    true
}
pub fn enabled(s: &State, op: Op) -> bool {
    match op {
        Op::Shared {account,token,owner} | Op::Exclusive {account,token,owner} =>
            account < CELLS && token < TOKENS && s.owner_live[account] && s.guards[token].is_none() && vacant(s,owner),
        Op::Deref {token} | Op::Drop {token} => token < TOKENS && s.guards[token].is_some(),
        Op::Write {token,index,..} => token < TOKENS && s.guards[token].is_some_and(|g| g.exclusive && index < s.payload[g.cell].descriptor.len),
        Op::Move {token,destination} => token < TOKENS && s.guards[token].is_some() && vacant(s,destination),
        Op::ErrorMoveDrop => true,
    }
}

/// Independent relational postcondition: the complete primitive footprint,
/// exact Result arm, counter/token identity, unchanged descriptors and contents
/// except the single bounded exclusive write. It also requires a valid successor.
/// No caller result, error mapping, copy, scope restoration or execution log.
pub fn primitive_relation(s: &State, op: Op, post: &State, reply: Reply) -> bool {
    if !array_eq(&post.accounts,&s.accounts) || !array_eq(&post.lamports,&s.lamports) || !array_eq(&post.owner_live,&s.owner_live) ||
       !array_eq(&post.allocated,&s.allocated) || !array_eq(&post.external,&s.external) || !array_eq(&post.ambient,&s.ambient) { return false; }
    let mut counter_cell = None;
    let mut counter_value = 0;
    let mut token_change = None;
    let mut guard_value = None;
    let mut write = None;
    let expected_reply = match op {
        Op::Shared {account,token,owner} | Op::Exclusive {account,token,owner} => {
            let c = s.accounts[account];
            let exclusive = matches!(op, Op::Exclusive {..});
            let ok = if exclusive { s.counter[c] == 0 } else { s.counter[c] >= 0 && s.counter[c] < i64::MAX };
            if ok {
                counter_cell = Some(c);
                counter_value = if exclusive { -1 } else { s.counter[c] + 1 };
                token_change = Some(token);
                guard_value = Some(Guard {cell:c,owner,exclusive,descriptor:s.payload[c].descriptor});
                Reply::Guard(token)
            } else { Reply::BorrowFailed }
        }
        Op::Deref {token} => Reply::Payload(s.payload[s.guards[token].unwrap().cell]),
        Op::Write {token,index,value} => { write = Some((s.guards[token].unwrap().cell,index,value)); Reply::Unit }
        Op::Move {token,destination} => {
            let mut g = s.guards[token].unwrap(); g.owner = destination;
            token_change = Some(token); guard_value = Some(g); Reply::Guard(token)
        }
        Op::Drop {token} => {
            let g = s.guards[token].unwrap();
            counter_cell = Some(g.cell);
            counter_value = if g.exclusive { 0 } else { s.counter[g.cell] - 1 };
            token_change = Some(token); Reply::Unit
        }
        Op::ErrorMoveDrop => Reply::BorrowFailed,
    };
    if reply != expected_reply { return false; }
    for c in 0..CELLS {
        if post.counter[c] != if counter_cell == Some(c) { counter_value } else { s.counter[c] } { return false; }
        if post.payload[c].descriptor != s.payload[c].descriptor { return false; }
        for i in 0..WIDTH {
            let expected = match write { Some((wc,wi,v)) if c == wc && i == wi => v, _ => s.payload[c].contents[i] };
            if post.payload[c].contents[i] != expected { return false; }
        }
    }
    for t in 0..TOKENS {
        if post.guards[t] != if token_change == Some(t) { guard_value } else { s.guards[t] } { return false; }
    }
    valid(post)
}

#[kani::requires(valid(&s))]
#[kani::requires(enabled(&s, op))]
#[kani::ensures(|out: &(State, Reply)| primitive_relation(&s, op, &out.0, out.1))]
pub fn step(s: State, op: Op) -> (State, Reply) {
    let mut next = s;
    let reply = match op {
        Op::Shared {account,token,owner} => {
            let c = s.accounts[account];
            if s.counter[c] < 0 || s.counter[c] == i64::MAX { Reply::BorrowFailed } else {
                next.counter[c] += 1;
                next.guards[token] = Some(Guard {cell:c,owner,exclusive:false,descriptor:s.payload[c].descriptor});
                Reply::Guard(token)
            }
        }
        Op::Exclusive {account,token,owner} => {
            let c = s.accounts[account];
            if s.counter[c] != 0 { Reply::BorrowFailed } else {
                next.counter[c] = -1;
                next.guards[token] = Some(Guard {cell:c,owner,exclusive:true,descriptor:s.payload[c].descriptor});
                Reply::Guard(token)
            }
        }
        Op::Deref {token} => Reply::Payload(s.payload[s.guards[token].unwrap().cell]),
        Op::Write {token,index,value} => {
            next.payload[s.guards[token].unwrap().cell].contents[index] = value; Reply::Unit
        }
        Op::Move {token,destination} => { next.guards[token].as_mut().unwrap().owner = destination; Reply::Guard(token) }
        Op::Drop {token} => {
            let g = next.guards[token].take().unwrap();
            if g.exclusive { next.counter[g.cell] = 0; } else { next.counter[g.cell] -= 1; }
            Reply::Unit
        }
        Op::ErrorMoveDrop => Reply::BorrowFailed,
    };
    (next,reply)
}

#[cfg(kani)]
mod checks {
    use super::*;
    fn state() -> State { let s = kani::any(); kani::assume(valid(&s)); s }
    fn input() -> (State, Op) { let s = state(); let op = kani::any(); kani::assume(enabled(&s,op)); (s,op) }
    fn acquire_input(exclusive: bool) -> (State,Op,usize,usize) {
        let s = state(); let a: usize = kani::any(); let t: usize = kani::any(); let o = kani::any();
        let op = if exclusive { Op::Exclusive {account:a,token:t,owner:o} } else { Op::Shared {account:a,token:t,owner:o} };
        kani::assume(enabled(&s,op)); (s,op,s.accounts[a],t)
    }
    fn guard_input(exclusive: bool) -> (State,usize,Guard) {
        let s = state(); let t:usize = kani::any(); kani::assume(t<TOKENS);
        kani::assume(s.guards[t].is_some()); let g = s.guards[t].unwrap(); kani::assume(g.exclusive==exclusive); (s,t,g)
    }
    #[kani::proof_for_contract(step)]
    #[kani::unwind(5)]
    fn step_contract() { let (s,op)=input(); step(s,op); }

    #[kani::proof] #[kani::unwind(5)]
    fn account_data_cell() {
        let s=state(); let a:usize=kani::any(); let b:usize=kani::any(); kani::assume(a<CELLS && b<CELLS);
        let handle = |a:usize| s.accounts[a];
        if s.accounts[a]==s.accounts[b] { assert_eq!(handle(a),handle(b)); }
        if s.owner_live[a] { assert_ne!(handle(a) as u64,s.lamports[a]); }
    }
    #[kani::proof] #[kani::unwind(5)]
    fn cell_payload() {
        let (s,t,g)=guard_input(kani::any()); let (n,r)=step(s,Op::Deref{token:t});
        assert_eq!(r,Reply::Payload(s.payload[g.cell])); assert_eq!(n,s);
    }
    #[kani::proof] #[kani::unwind(5)]
    fn cell_counter() { let s=state(); assert!(valid(&s)); }
    #[kani::proof] #[kani::unwind(5)]
    fn shared_ok() {
        let (s,op,c,t)=acquire_input(false); kani::assume(s.counter[c]>=0 && s.counter[c]<i64::MAX);
        let (n,r)=step(s,op); assert_eq!(r,Reply::Guard(t)); assert_eq!(n.counter[c],s.counter[c]+1);
        let g=n.guards[t].unwrap(); assert_eq!(g.cell,c); assert!(!g.exclusive); assert_eq!(g.descriptor,s.payload[c].descriptor); assert!(valid(&n));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn shared_err() {
        let (s,op,c,_)=acquire_input(false); kani::assume(s.counter[c]<0 || s.counter[c]==i64::MAX);
        assert_eq!(step(s,op),(s,Reply::BorrowFailed)); kani::cover!(s.counter[c]<0); kani::cover!(s.counter[c]==i64::MAX);
    }
    #[kani::proof] #[kani::unwind(5)]
    fn exclusive_ok() {
        let (s,op,c,t)=acquire_input(true); kani::assume(s.counter[c]==0); let (n,r)=step(s,op);
        assert_eq!(r,Reply::Guard(t)); assert_eq!(n.counter[c],-1); assert!(n.guards[t].unwrap().exclusive); assert!(valid(&n));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn exclusive_err() {
        let (s,op,c,_)=acquire_input(true); kani::assume(s.counter[c]!=0); assert_eq!(step(s,op),(s,Reply::BorrowFailed));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn shared_deref() {
        let (s,t,g)=guard_input(false); assert_eq!(step(s,Op::Deref{token:t}),(s,Reply::Payload(s.payload[g.cell])));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn exclusive_deref() {
        let (s,t,g)=guard_input(true); assert_eq!(step(s,Op::Deref{token:t}),(s,Reply::Payload(s.payload[g.cell])));
        let i:usize=kani::any(); kani::assume(i<s.payload[g.cell].descriptor.len); let v=kani::any();
        let (n,r)=step(s,Op::Write{token:t,index:i,value:v}); assert_eq!(r,Reply::Unit);
        assert_eq!(n.payload[g.cell].contents[i],v); assert_eq!(n.payload[g.cell].descriptor,g.descriptor); assert!(valid(&n));
        for c in 0..CELLS { for j in 0..WIDTH { if c!=g.cell || j!=i { assert_eq!(n.payload[c].contents[j],s.payload[c].contents[j]); } } }
    }
    #[kani::proof] #[kani::unwind(5)]
    fn guard_move() {
        let (s,t,g)=guard_input(kani::any()); let o=kani::any(); let op=Op::Move{token:t,destination:o}; kani::assume(enabled(&s,op));
        let (n,r)=step(s,op); assert_eq!(r,Reply::Guard(t)); assert!(array_eq(&n.counter,&s.counter)); assert!(array_eq(&n.payload,&s.payload));
        assert_eq!(n.guards[t],Some(Guard{owner:o,..g})); for h in n.guards { if let Some(h)=h { assert_ne!(h.owner,g.owner); } } assert!(valid(&n));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn shared_drop() {
        let (s,t,g)=guard_input(false); let (n,_)=step(s,Op::Drop{token:t});
        assert_eq!(n.counter[g.cell],s.counter[g.cell]-1); assert!(n.guards[t].is_none()); assert!(array_eq(&n.payload,&s.payload)); assert!(valid(&n));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn exclusive_drop() {
        let (s,t,g)=guard_input(true); assert_eq!(s.counter[g.cell],-1); let (n,_)=step(s,Op::Drop{token:t});
        assert_eq!(n.counter[g.cell],0); assert!(n.guards[t].is_none()); assert!(array_eq(&n.payload,&s.payload)); assert!(valid(&n));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn error_move_drop() { let s=state(); assert_eq!(step(s,Op::ErrorMoveDrop),(s,Reply::BorrowFailed)); }
    #[kani::proof] #[kani::unwind(5)]
    fn borrow_frame() {
        let (s,op)=input(); let (n,r)=step(s,op); assert!(primitive_relation(&s,op,&n,r));
    }
    #[kani::proof] #[kani::unwind(5)]
    fn guard_liveness() {
        let (s,t,g)=guard_input(kani::any()); assert!(s.allocated[g.cell]); assert_eq!(g.descriptor,s.payload[g.cell].descriptor);
        let op:Op=kani::any(); kani::assume(enabled(&s,op)); let (n,_)=step(s,op);
        if let Some(h)=n.guards[t] { assert!(n.allocated[h.cell]); assert_eq!(h.cell,g.cell); assert_eq!(h.descriptor,g.descriptor); }
    }
    #[kani::proof] #[kani::unwind(5)]
    #[kani::stub_verified(step)]
    fn verified_stub_schedule() {
        let mut s=state(); let a:usize=kani::any(); kani::assume(a<CELLS); let c=s.accounts[a];
        kani::assume(s.owner_live[a] && s.counter[c]==0 && s.guards[0].is_none() && s.guards[1].is_none() && vacant(&s,100) && vacant(&s,101));
        let original=s; let (n,r)=step(s,Op::Exclusive{account:a,token:0,owner:100}); assert_eq!(r,Reply::Guard(0)); s=n;
        let (n,r)=step(s,Op::Shared{account:a,token:1,owner:101}); assert_eq!(r,Reply::BorrowFailed); s=n;
        let (n,_)=step(s,Op::Move{token:0,destination:101}); s=n;
        let (n,_)=step(s,Op::Drop{token:0}); assert_eq!(n,original);
        kani::cover!(true);
    }
}
