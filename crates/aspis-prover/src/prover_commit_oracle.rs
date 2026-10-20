//! D92 relational ROM, indexed by concatenated bytes (hashv slice boundaries
//! are not part of the SHA-256 message). Every new point has an unconstrained
//! digest; collisions are permitted. Both sides use this one table, never a
//! reset between sides. This is an oracle model, not a SHA-256 theorem.
const POINTS: usize = 4;
const BYTES: usize = 512;
#[derive(Clone, Copy)]
struct Entry { input: [u8; BYTES], len: usize, digest: [u8; 32] }
const EMPTY: Entry = Entry { input: [0; BYTES], len: 0, digest: [0; 32] };
struct Oracle { entries: [Entry; POINTS], used: usize, calls: usize, budget: usize }
static mut ORACLE: Oracle = Oracle { entries: [EMPTY; POINTS], used: 0, calls: 0, budget: 0 };

pub(crate) fn reset(budget: usize) {
    // Harnesses are single-threaded; no reference escapes this function.
    unsafe { ORACLE = Oracle { entries: [EMPTY; POINTS], used: 0, calls: 0, budget }; }
}
pub(crate) fn query(parts: &[&[u8]]) -> [u8; 32] {
    let mut input = [0; BYTES];
    let mut len = 0;
    for part in parts {
        for byte in *part {
            assert!(len < BYTES, "oracle input capacity");
            input[len] = *byte;
            len += 1;
        }
    }
    unsafe {
        let table = &mut *core::ptr::addr_of_mut!(ORACLE);
        assert!(table.calls < table.budget, "harness query budget");
        table.calls += 1;
        for i in 0..POINTS {
            if i < table.used && table.entries[i].len == len {
                let mut equal = true;
                for j in 0..BYTES {
                    equal &= table.entries[i].input[j] == input[j];
                }
                if equal { return table.entries[i].digest; }
            }
        }
        assert!(table.used < POINTS, "oracle point capacity");
        let digest = kani::any();
        table.entries[table.used] = Entry { input, len, digest };
        table.used += 1;
        digest
    }
}

#[kani::proof]
#[kani::unwind(514)]
fn regrouping_and_repeated_points() {
    reset(3);
    let a: [u8; 32] = kani::any();
    let b: [u8; 32] = kani::any();
    let mut joined = [0; 64];
    joined[..32].copy_from_slice(&a);
    joined[32..].copy_from_slice(&b);
    let first = query(&[&a, &b]);
    assert_eq!(first, query(&[&joined]));
    assert_eq!(first, query(&[&a, &[], &b]));
}

#[kani::proof]
#[kani::unwind(514)]
#[kani::stub(crate::host_hashv, query)]
fn private_leaf_c1() {
    reset(2);
    let value: [u8; 416] = kani::any();
    let salt: [u8; 32] = kani::any();
    let actual = aspis_core::state_only_private_merkle::private_leaf_hash(crate::HOST_HASH, 0x71, &value, &salt);
    let mut bytes = [0; 450];
    bytes[0] = 0x10;
    bytes[1] = 0x71;
    bytes[2..418].copy_from_slice(&value);
    bytes[418..].copy_from_slice(&salt);
    assert_eq!(actual, crate::HOST_HASH(&[&bytes]));
}

#[kani::proof]
#[kani::unwind(514)]
#[kani::stub(crate::host_hashv, query)]
fn private_leaf_c2() {
    reset(2);
    let value: [u8; 192] = kani::any();
    let salt: [u8; 32] = kani::any();
    let actual = aspis_core::state_only_private_merkle::private_leaf_hash(crate::HOST_HASH, 0xf1, &value, &salt);
    let mut bytes = [0; 226];
    bytes[0] = 0x10;
    bytes[1] = 0xf1;
    bytes[2..194].copy_from_slice(&value);
    bytes[194..].copy_from_slice(&salt);
    assert_eq!(actual, crate::HOST_HASH(&[&bytes]));
}

#[kani::proof]
#[kani::unwind(514)]
#[kani::stub(crate::host_hashv, query)]
fn private_leaf_folded() {
    reset(2);
    let value: [u8; 128] = kani::any();
    let salt: [u8; 32] = kani::any();
    let actual = aspis_core::state_only_private_merkle::private_leaf_hash(crate::HOST_HASH, 0x72, &value, &salt);
    let mut bytes = [0; 162];
    bytes[0] = 0x10;
    bytes[1] = 0x72;
    bytes[2..130].copy_from_slice(&value);
    bytes[130..].copy_from_slice(&salt);
    assert_eq!(actual, crate::HOST_HASH(&[&bytes]));
}
