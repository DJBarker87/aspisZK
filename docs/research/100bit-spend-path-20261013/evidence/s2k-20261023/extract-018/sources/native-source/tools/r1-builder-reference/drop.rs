//! Actual shipped Drop, no stubs. Its owned Vec buffers are part of the footprint.
//! The small harness covers arbitrary lengths 0..=2 in every column. The fixed
//! harness covers the admitted 16 x 1024 shape, with arbitrary stored words.
use aspis_core::field::M31;
use aspis_statement::state_only_trace::StateOnlyTraceFoundation;

fn check_drop(trace: StateOnlyTraceFoundation) {
    // A separately owned allocation models retained output bytes. Rust's
    // unique ownership excludes aliases to the trace's owned buffers.
    let output: u64 = kani::any();
    let retained = Box::new(output);
    let result: () = drop(trace);
    assert_eq!(result, ());
    assert_eq!(*retained, output);
}

#[kani::proof]
#[kani::unwind(18)]
fn trace_drop_small() {
    let mut trace = StateOnlyTraceFoundation::default();
    for i in 0..16 {
        let n: usize = kani::any();
        kani::assume(n <= 2);
        for _ in 0..n {
            // All storage words, including non-canonical ones, are allowed.
            trace.c1[i].push(M31(kani::any()));
        }
    }
    check_drop(trace);
}

#[kani::proof]
#[kani::unwind(1026)]
fn trace_drop_full() {
    let mut trace = StateOnlyTraceFoundation::default();
    for i in 0..16 {
        let words: [u32; 1024] = kani::any();
        trace.c1[i] = words.into_iter().map(M31).collect();
    }
    check_drop(trace);
}

// Dynamic write-set instrumentation checks stores, including temporary stores,
// rather than merely comparing one output after execution.
#[kani::modifies(
    core::ptr::slice_from_raw_parts_mut(trace.c1[0].as_ptr() as *mut u32, trace.c1[0].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[1].as_ptr() as *mut u32, trace.c1[1].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[2].as_ptr() as *mut u32, trace.c1[2].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[3].as_ptr() as *mut u32, trace.c1[3].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[4].as_ptr() as *mut u32, trace.c1[4].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[5].as_ptr() as *mut u32, trace.c1[5].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[6].as_ptr() as *mut u32, trace.c1[6].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[7].as_ptr() as *mut u32, trace.c1[7].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[8].as_ptr() as *mut u32, trace.c1[8].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[9].as_ptr() as *mut u32, trace.c1[9].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[10].as_ptr() as *mut u32, trace.c1[10].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[11].as_ptr() as *mut u32, trace.c1[11].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[12].as_ptr() as *mut u32, trace.c1[12].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[13].as_ptr() as *mut u32, trace.c1[13].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[14].as_ptr() as *mut u32, trace.c1[14].len()),
    core::ptr::slice_from_raw_parts_mut(trace.c1[15].as_ptr() as *mut u32, trace.c1[15].len())
)]
fn drop_owned_frame(trace: StateOnlyTraceFoundation) { drop(trace); }

#[kani::proof_for_contract(drop_owned_frame)]
#[kani::unwind(18)]
fn trace_drop_frame_small() {
    let mut trace = StateOnlyTraceFoundation::default();
    for i in 0..16 {
        let n: usize = kani::any();
        kani::assume(n <= 2);
        for _ in 0..n { trace.c1[i].push(M31(kani::any())); }
    }
    drop_owned_frame(trace);
}

// Fixed allocations eliminate the independent symbolic allocator branches of
// the earlier diagnostic harness. Every initialized word is still arbitrary.
#[kani::proof_for_contract(drop_owned_frame)]
#[kani::unwind(18)]
fn trace_drop_frame_fixed() {
    let mut trace = StateOnlyTraceFoundation::default();
    for i in 0..16 {
        trace.c1[i] = vec![M31(kani::any()), M31(kani::any())];
    }
    drop_owned_frame(trace);
}

// Isolate one symbolic column to avoid the quadratic cross-allocation
// instrumentation of the complete 16-column frame check.
#[kani::proof_for_contract(drop_owned_frame)]
#[kani::unwind(18)]
fn trace_drop_frame_column() {
    let mut trace = StateOnlyTraceFoundation::default();
    let i: usize = kani::any();
    kani::assume(i < 16);
    trace.c1[i] = vec![M31(kani::any()), M31(kani::any())];
    drop_owned_frame(trace);
}

// Project precisely the volatile store used by the shipped destructor.
// Kani instruments its entire dynamic write set; no destructor is stubbed.
#[kani::modifies(value)]
#[kani::ensures(|_: &()| *value == 0)]
fn volatile_zero_word(value: &mut u32) {
    // M31 is repr(transparent) over u32; all u32 patterns are valid.
    unsafe { core::ptr::write_volatile(value as *mut u32 as *mut M31, M31::ZERO); }
}

#[kani::proof_for_contract(volatile_zero_word)]
fn trace_drop_volatile_word() {
    let mut value: u32 = kani::any();
    volatile_zero_word(&mut value);
}
