//! D92 relational ROM, indexed by concatenated bytes (hashv slice boundaries
//! are not part of the SHA-256 message). Every new point has an unconstrained
//! digest; collisions are permitted. Both sides use this one table, never a
//! reset between sides. This is an oracle model, not a SHA-256 theorem.
const POINTS: usize = 4;
const BYTES: usize = 514;
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
#[kani::unwind(516)]
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
#[kani::unwind(516)]
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
#[kani::unwind(516)]
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
#[kani::unwind(516)]
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

/// Check the actual global function-pointer route is replaced by the shared
/// oracle, rather than merely checking the oracle through direct calls.
#[kani::proof]
#[kani::unwind(516)]
#[kani::stub(crate::host_hashv, query)]
fn callback_stub_is_active() {
    reset(2);
    let input: [u8; 32] = kani::any();
    let callback: aspis_core::HashFn = crate::HOST_HASH;
    let first = callback(&[&input]);
    assert_eq!(first, query(&[&input]));
    unsafe {
        assert_eq!(ORACLE.calls, 2);
        assert_eq!(ORACLE.used, 1);
    }
}

// Exact finite ROM for one QM31 call from an arbitrary valid word slot.
// Its four scalar calls can touch at most nine consecutive blocks. Preassigning independent
// arbitrary answers to these distinct messages is the memoised oracle law;
// no digest distinctness or SHA property is assumed.
struct ExpanderOracle {
    domain: &'static [u8], seed: [u8; 32], counter: u64,
    answers: [[u8; 32]; 9],
}
static mut EXPANDER: ExpanderOracle = ExpanderOracle {
    domain: &[], seed: [0;32], counter: 0, answers: [[0;32];9],
};
pub(crate) fn reset_expander(domain: &'static [u8], seed: [u8;32], counter: u64) {
    unsafe { EXPANDER = ExpanderOracle { domain, seed, counter, answers: kani::any() }; }
}
pub(crate) fn expander_query(parts: &[&[u8]]) -> [u8;32] {
    // Both shipped expanders and the owned reference use exactly these
    // three slices. Assert the complete frame at every reachable call.
    assert_eq!(parts.len(), 3);
    unsafe {
        let table = &*core::ptr::addr_of!(EXPANDER);
        assert_eq!(parts[0].len(), table.domain.len());
        assert_eq!(parts[1].len(), 32);
        assert_eq!(parts[2].len(), 8);
        for i in 0..table.domain.len() { assert_eq!(parts[0][i], table.domain[i]); }
        for i in 0..32 { assert_eq!(parts[1][i], table.seed[i]); }
        let counter = u64::from_le_bytes(parts[2].try_into().unwrap());
        let index = counter.wrapping_sub(table.counter);
        assert!(index < 9, "QM31 call oracle domain");
        table.answers[index as usize]
    }
}

pub(crate) fn expander_domain(domain: &[u8], seed: [u8;32], counter: u64, word: usize) -> bool {
    unsafe {
        let table = &*core::ptr::addr_of!(EXPANDER);
        table.domain == domain && table.seed == seed &&
            (word < 8 || counter.wrapping_sub(table.counter) < 9)
    }
}

#[kani::proof]
#[kani::unwind(84)]
fn expander_rom_memo() {
    let source: bool = kani::any();
    let domain: &'static [u8] = if source { b"aspis:state-only:profile21:source-expand:v1" }
        else { b"aspis:state-only:private-mask-expand:v1" };
    let seed: [u8;32] = kani::any();
    let base: u64 = kani::any();
    reset_expander(domain, seed, base);
    for i in 0u64..9 {
        let counter = base.wrapping_add(i);
        assert_eq!(counter.wrapping_sub(base), i);
        let answer = expander_query(&[domain, &seed, &counter.to_le_bytes()]);
        assert_eq!(answer, expander_query(&[domain, &seed, &counter.to_le_bytes()]));
    }
}

// The selected binary R1 tree encodes 26 base lanes and lane D in C1,
// and two QM31 lanes in C2. These are not the legacy 416/192-byte cases.
#[kani::proof]
#[kani::unwind(516)]
#[kani::stub(crate::host_hashv, query)]
fn selected_c1_leaf_frame() {
    reset(2);
    let value: [u8;480] = kani::any();
    let salt: [u8;32] = kani::any();
    let actual = aspis_core::state_only_private_merkle::private_leaf_hash(
        crate::HOST_HASH, 0x71, &value, &salt);
    let mut bytes = [0u8;514];
    bytes[0] = 0x10; bytes[1] = 0x71;
    bytes[2..482].copy_from_slice(&value);
    bytes[482..].copy_from_slice(&salt);
    assert_eq!(actual, crate::HOST_HASH(&[&bytes]));
}
#[kani::proof]
#[kani::unwind(516)]
#[kani::stub(crate::host_hashv, query)]
fn selected_c2_leaf_frame() {
    reset(2);
    let value: [u8;128] = kani::any();
    let salt: [u8;32] = kani::any();
    let actual = aspis_core::state_only_private_merkle::private_leaf_hash(
        crate::HOST_HASH, 0xf1, &value, &salt);
    let mut bytes = [0u8;162];
    bytes[0] = 0x10; bytes[1] = 0xf1;
    bytes[2..130].copy_from_slice(&value);
    bytes[130..].copy_from_slice(&salt);
    assert_eq!(actual, crate::HOST_HASH(&[&bytes]));
}

pub(crate) fn known_domain(domain: &[u8]) -> bool {
    domain == b"aspis:state-only:private-mask-expand:v1" ||
        domain == b"aspis:state-only:profile21:source-expand:v1"
}
pub(crate) fn scalar_domain(domain: &[u8], seed: [u8;32], counter: u64) -> bool {
    unsafe {
        let table = &*core::ptr::addr_of!(EXPANDER);
        table.domain == domain && table.seed == seed && counter.wrapping_sub(table.counter) <= 6
    }
}
pub(crate) fn expander_block(counter: u64) -> [u8;32] {
    unsafe {
        let table = &*core::ptr::addr_of!(EXPANDER);
        let index = counter.wrapping_sub(table.counter);
        assert!(index < 9);
        table.answers[index as usize]
    }
}
