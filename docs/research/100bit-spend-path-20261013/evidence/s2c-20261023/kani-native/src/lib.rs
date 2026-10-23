#![cfg(kani)]
#![allow(non_snake_case)]
//! Individual native operations only. These harnesses do not execute stage1.
//! No foreign Ref/RefMut representation is fabricated or havoced.
mod statement;
use aspis_statement::pool_v1::PoolV1PairForestTerminalStatementV1;

// Match the pinned release bump deallocator; this is an explicit allocator
// dispatch hypothesis, outside S2TrustedSdkBorrow. Its actual body is executed.
unsafe fn S2C_release_dealloc(pointer: *mut u8, layout: std::alloc::Layout) {
    let allocator = solana_program_entrypoint::BumpAllocator {
        start: solana_program_entrypoint::HEAP_START_ADDRESS as usize, len: 256*1024,
    };
    std::alloc::GlobalAlloc::dealloc(&allocator, pointer, layout);
}

// Empty bodies force the compiler's implicit parameter Drop, as in the suffix.
#[inline(never)]
fn S2C_vec_drop(_reply: Vec<u8>) {}
#[inline(never)]
fn S2C_box_drop(_statement: Box<PoolV1PairForestTerminalStatementV1>) {}

mod S2C_native {
    use super::*;
    #[kani::proof]
    #[kani::unwind(1772)]
    fn checkpoint_copy_byte() {
        let source: [u8;1768] = kani::any();
        let mut target: [u8;1768] = kani::any();
        let index: usize = kani::any(); kani::assume(index < 1768);
        let source_byte = source[index];
        target.as_mut_slice().copy_from_slice(source.as_slice());
        assert_eq!(target[index], source_byte);
        assert_eq!(source[index], source_byte);
        kani::cover!(index==0);
        kani::cover!(index==1767);
    }
    // One protected region, one arbitrary observed index, one native Drop.
    fn vec_region<const N: usize>() {
        let region: [u8;N] = kani::any();
        let index: usize = kani::any(); kani::assume(index < N);
        let before = region[index];
        let reply = kani::vec::exact_vec::<u8,1768>();
        S2C_vec_drop(reply);
        assert_eq!(region[index],before);
    }
    fn box_region<const N: usize>() {
        let region: [u8;N] = kani::any();
        let index: usize = kani::any(); kani::assume(index < N);
        let before = region[index];
        // The actual current production type, both variants, arbitrary fields.
        assert!(!std::mem::needs_drop::<PoolV1PairForestTerminalStatementV1>());
        let value = Box::new(statement::statement());
        S2C_box_drop(value);
        assert_eq!(region[index],before);
    }
    #[kani::proof] #[kani::unwind(8)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn vec_drop_proof() { vec_region::<58295>(); }
    #[kani::proof] #[kani::unwind(8)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn vec_drop_public() { vec_region::<1880>(); }
    #[kani::proof] #[kani::unwind(8)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn vec_drop_checkpoint() { vec_region::<1768>(); }
    #[kani::proof] #[kani::unwind(48)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn box_drop_proof() { box_region::<58295>(); }
    #[kani::proof] #[kani::unwind(48)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn box_drop_public() { box_region::<1880>(); }
    #[kani::proof] #[kani::unwind(48)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn box_drop_checkpoint() { box_region::<1768>(); }
}

// Exact adopted bounded primitive source; verification evidence is inherited.
#[path="S2C_trusted.rs"] mod S2C_trusted;
mod S2C_guard {
    use super::S2C_trusted::*;
    fn drop_region(exclusive: bool) {
        let state: State = kani::any(); kani::assume(valid(&state));
        let token: usize = kani::any(); kani::assume(token < TOKENS);
        kani::assume(state.guards[token].is_some());
        let guard = state.guards[token].unwrap(); kani::assume(guard.exclusive == exclusive);
        let observed_cell: usize = kani::any(); kani::assume(observed_cell < CELLS);
        let observed_index: usize = kani::any(); kani::assume(observed_index < WIDTH);
        let out = step(state, Op::Drop{token});
        assert_eq!(out.1, Reply::Unit);
        assert_eq!(out.0.payload[observed_cell].contents[observed_index],state.payload[observed_cell].contents[observed_index]);
        assert_eq!(out.0.payload[observed_cell].descriptor,state.payload[observed_cell].descriptor);
        for i in 0..4 { assert_eq!(out.0.ambient[i],state.ambient[i]); }
        for i in 0..CELLS {
            assert_eq!(out.0.accounts[i],state.accounts[i]);
            assert_eq!(out.0.lamports[i],state.lamports[i]);
            assert_eq!(out.0.allocated[i],state.allocated[i]);
        }
        assert!(out.0.guards[token].is_none());
        assert_eq!(out.0.counter[guard.cell],if exclusive {0} else {state.counter[guard.cell]-1});
        kani::cover!(observed_cell==guard.cell);
        kani::cover!(observed_cell!=guard.cell);
    }
    #[kani::proof] #[kani::unwind(5)]
    #[kani::stub_verified(step)]
    fn shared_drop_region() {drop_region(false);}
    #[kani::proof] #[kani::unwind(5)]
    #[kani::stub_verified(step)]
    fn exclusive_drop_region() {drop_region(true);}
}

// Per-owner write-set checks. The inner function performs implicit destruction
// before this wrapper's contract boundary; no parameter survives to be dropped
// after the postcondition. This avoids the inherited pre-destruction probe bug.
#[kani::requires(reply.len()==1768)]
#[kani::modifies()]
fn S2C_checked_vec_drop(reply: Vec<u8>) { S2C_vec_drop(reply); }
#[kani::modifies()]
fn S2C_checked_box_drop(value: Box<PoolV1PairForestTerminalStatementV1>) { S2C_box_drop(value); }
mod S2C_owner_contract {
    use super::*;
    #[kani::proof_for_contract(S2C_checked_vec_drop)] #[kani::unwind(8)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn vec_drop_writes() { S2C_checked_vec_drop(kani::vec::exact_vec::<u8,1768>()); }
    #[kani::proof_for_contract(S2C_checked_box_drop)] #[kani::unwind(48)]
    #[kani::stub(std::alloc::dealloc, S2C_release_dealloc)]
    fn box_drop_writes() { S2C_checked_box_drop(Box::new(statement::statement())); }
}
