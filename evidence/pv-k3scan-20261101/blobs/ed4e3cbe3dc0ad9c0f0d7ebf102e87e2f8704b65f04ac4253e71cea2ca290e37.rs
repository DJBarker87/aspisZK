//! Indexed, extraction-friendly external layer. Included only in proof builds.
use super::*;

pub fn mat4_reference(values: &mut [M31]) {
    let x = [values[0].0 as u64, values[1].0 as u64,
             values[2].0 as u64, values[3].0 as u64];
    let matrix = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
    let mut row = 0;
    while row < 4 {
        let mut sum = 0u64;
        let mut col = 0;
        while col < 4 {
            sum += matrix[row][col] * x[col];
            col += 1;
        }
        values[row] = M31::reduce_u62(sum);
        row += 1;
    }
}

pub fn external_reference(state: &mut [M31; 16]) {
    let mut block = 0;
    while block < 4 {
        let base = block * 4;
        let mut chunk = [state[base], state[base+1], state[base+2], state[base+3]];
        mat4_reference(&mut chunk);
        let mut lane = 0;
        while lane < 4 {
            state[base+lane] = chunk[lane];
            lane += 1;
        }
        block += 1;
    }
    let mut sums = [0u64; 4];
    let mut col = 0;
    while col < 4 {
        let mut row = 0;
        while row < 4 {
            sums[col] += state[row*4+col].0 as u64;
            row += 1;
        }
        col += 1;
    }
    let mut lane = 0;
    while lane < 16 {
        state[lane] = M31::reduce_u62(state[lane].0 as u64 + sums[lane % 4]);
        lane += 1;
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn mat4_shipped_equals_reference() {
    let mut actual = kani::any::<[u32; 4]>().map(M31);
    let mut expected = actual;
    apply_mat4_lazy(&mut actual);
    mat4_reference(&mut expected);
    assert_eq!(actual, expected);
}

// The stub is exactly the four-lane callee proved above, for all u32 inputs.
// This proof composes that result; it does not postulate arbitrary hash outputs.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(crate::poseidon2::apply_mat4_lazy, mat4_reference)]
fn external_shipped_equals_reference() {
    let mut actual = kani::any::<[u32; 16]>().map(M31);
    let mut expected = actual;
    external_linear_lazy(&mut actual);
    external_reference(&mut expected);
    assert_eq!(actual, expected);
}

// Relational abstraction of the four already-proved mat4 calls. Record every
// argument before replacing its result by a shared arbitrary row. The reference
// must supply the identical arguments in the identical call order. This checks
// the pure-call congruence side condition instead of assuming equal arguments.
#[cfg(kani)]
static mut MAT4_INPUTS: [[M31; 4]; 4] = [[M31::ZERO; 4]; 4];
#[cfg(kani)]
static mut MAT4_OUTPUTS: [[M31; 4]; 4] = [[M31::ZERO; 4]; 4];
#[cfg(kani)]
static mut ACTUAL_CALL: usize = 0;
#[cfg(kani)]
static mut REFERENCE_CALL: usize = 0;

#[cfg(kani)]
fn record_mat4(values: &mut [M31]) {
    assert_eq!(values.len(), 4);
    unsafe {
        assert!(ACTUAL_CALL < 4);
        for i in 0..4 {
            MAT4_INPUTS[ACTUAL_CALL][i] = values[i];
            values[i] = MAT4_OUTPUTS[ACTUAL_CALL][i];
        }
        ACTUAL_CALL += 1;
    }
}

#[cfg(kani)]
fn check_mat4(values: &mut [M31]) {
    assert_eq!(values.len(), 4);
    unsafe {
        assert!(REFERENCE_CALL < 4);
        for i in 0..4 {
            assert_eq!(values[i], MAT4_INPUTS[REFERENCE_CALL][i]);
            values[i] = MAT4_OUTPUTS[REFERENCE_CALL][i];
        }
        REFERENCE_CALL += 1;
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(crate::poseidon2::apply_mat4_lazy, record_mat4)]
#[kani::stub(crate::poseidon2::builder_reference::mat4_reference, check_mat4)]
fn external_call_trace_and_outputs() {
    let mut actual = kani::any::<[u32; 16]>().map(M31);
    let mut expected = actual;
    unsafe {
        MAT4_OUTPUTS = kani::any::<[[u32; 4]; 4]>().map(|r| r.map(M31));
        ACTUAL_CALL = 0;
        REFERENCE_CALL = 0;
    }
    external_linear_lazy(&mut actual);
    external_reference(&mut expected);
    unsafe {
        assert_eq!(ACTUAL_CALL, 4);
        assert_eq!(REFERENCE_CALL, 4);
    }
    assert_eq!(actual, expected);
}

// Owned reference avoids carrying a mutable slice borrow across a nested loop.
pub fn mat4_owned(x: [M31; 4]) -> [M31; 4] {
    let a = x[0].0 as u64;
    let b = x[1].0 as u64;
    let c = x[2].0 as u64;
    let d = x[3].0 as u64;
    [M31::reduce_u62(2*a+3*b+c+d), M31::reduce_u62(a+2*b+3*c+d),
     M31::reduce_u62(a+b+2*c+3*d), M31::reduce_u62(3*a+b+c+2*d)]
}

pub fn external_owned(mut state: [M31; 16]) -> [M31; 16] {
    let mut block = 0;
    while block < 4 {
        let base = block*4;
        let x = mat4_owned([state[base], state[base+1], state[base+2], state[base+3]]);
        state[base] = x[0];
        state[base+1] = x[1];
        state[base+2] = x[2];
        state[base+3] = x[3];
        block += 1;
    }
    let mut sums = [0u64; 4];
    let mut col = 0;
    while col < 4 {
        sums[col] = state[col].0 as u64 + state[col+4].0 as u64
                  + state[col+8].0 as u64 + state[col+12].0 as u64;
        col += 1;
    }
    let mut lane = 0;
    while lane < 16 {
        state[lane] = M31::reduce_u62(state[lane].0 as u64 + sums[lane % 4]);
        lane += 1;
    }
    state
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn mat4_owned_equals_shipped() {
    let mut actual = kani::any::<[u32; 4]>().map(M31);
    let expected = mat4_owned(actual);
    apply_mat4_lazy(&mut actual);
    assert_eq!(actual, expected);
}

#[cfg(kani)]
fn check_mat4_owned(mut x: [M31; 4]) -> [M31; 4] {
    check_mat4(&mut x);
    x
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(crate::poseidon2::apply_mat4_lazy, record_mat4)]
#[kani::stub(crate::poseidon2::builder_reference::mat4_owned, check_mat4_owned)]
fn external_owned_call_trace_and_outputs() {
    let mut actual = kani::any::<[u32; 16]>().map(M31);
    let input = actual;
    unsafe {
        MAT4_OUTPUTS = kani::any::<[[u32; 4]; 4]>().map(|r| r.map(M31));
        ACTUAL_CALL = 0;
        REFERENCE_CALL = 0;
    }
    external_linear_lazy(&mut actual);
    let expected = external_owned(input);
    unsafe {
        assert!(ACTUAL_CALL == 4);
        assert!(REFERENCE_CALL == 4);
    }
    assert_eq!(actual, expected);
}

// Unstubbed full external-layer association for the extracted owned callback.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(17)]
fn pv_srcid3_external_owned_unstubbed() {
    let mut actual = kani::any::<[u32; 16]>().map(M31);
    let expected = external_owned(actual);
    external_linear_lazy(&mut actual);
    assert_eq!(actual, expected);
}
