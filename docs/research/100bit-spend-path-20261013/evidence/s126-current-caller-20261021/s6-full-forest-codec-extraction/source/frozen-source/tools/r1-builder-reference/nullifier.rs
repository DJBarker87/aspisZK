//! Owned P6 route for the higher-ranked borrowed nullifier callback.
use super::*;

pub fn preimage_owned(key: Digest, salt: Digest) -> [M31; 16] {
    [key[0], key[1], key[2], key[3], key[4], key[5], key[6], key[7],
     salt[0], salt[1], salt[2], salt[3], salt[4], salt[5], salt[6], salt[7]]
}

pub fn derive_nullifier_owned_with<H>(key: Digest, salt: Digest, mut hash: H) -> Digest
where H: FnMut(M31, [M31; 16]) -> Digest {
    hash(DOMAIN_NULLIFIER, preimage_owned(key, salt))
}

fn hash_owned(domain: M31, input: [M31;16]) -> Digest {
    hash_fields(domain,&input)
}

pub fn derive_nullifier_owned(key: Digest, salt: Digest) -> Digest {
    derive_nullifier_owned_with(key,salt,hash_owned)
}

#[cfg(kani)]
mod proofs {
    use super::*;
    #[derive(Clone, Copy)]
    struct Entry { domain: M31, input: [M31;16], output: Digest }
    const EMPTY: Entry = Entry { domain: M31::ZERO, input: [M31::ZERO;16], output: [M31::ZERO;8] };
    static mut TABLE: [Entry; 2] = [EMPTY;2];
    static mut USED: usize = 0;
    static mut CALLS: usize = 0;
    fn reset() { unsafe { TABLE = [EMPTY;2]; USED = 0; CALLS = 0; } }
    // One table is shared by both programs, without resetting between sides.
    // Domain is part of the key; fresh answers are unrestricted, including collisions.
    fn oracle(domain: M31, input: &[M31]) -> Digest {
        assert_eq!(input.len(),16);
        let mut owned = [M31::ZERO;16];
        for i in 0..16 { owned[i] = input[i]; }
        unsafe {
            assert!(CALLS < 2); CALLS += 1;
            for i in 0..2 {
                let mut equal = true;
                for j in 0..16 { equal &= TABLE[i].input[j] == owned[j]; }
                if i < USED && TABLE[i].domain == domain && equal {
                    return TABLE[i].output;
                }
            }
            assert!(USED < 2);
            let output = kani::any::<[u32;8]>().map(M31);
            TABLE[USED] = Entry { domain, input: owned, output }; USED += 1;
            output
        }
    }
    #[kani::ensures(|result: &[u32;16]| result[0] == key[0] &&
        result[1] == key[1] &&
        result[2] == key[2] &&
        result[3] == key[3] &&
        result[4] == key[4] &&
        result[5] == key[5] &&
        result[6] == key[6] &&
        result[7] == key[7] &&
        result[8] == salt[0] &&
        result[9] == salt[1] &&
        result[10] == salt[2] &&
        result[11] == salt[3] &&
        result[12] == salt[4] &&
        result[13] == salt[5] &&
        result[14] == salt[6] &&
        result[15] == salt[7])]
    fn preimage_words(key: [u32;8],salt: [u32;8]) -> [u32;16] {
        [key[0],key[1],key[2],key[3],key[4],key[5],key[6],key[7],
         salt[0],salt[1],salt[2],salt[3],salt[4],salt[5],salt[6],salt[7]]
    }
    fn preimage_from_words(key: Digest,salt: Digest) -> [M31;16] {
        preimage_words(key.map(|x| x.0),salt.map(|x| x.0)).map(M31)
    }
    #[kani::proof_for_contract(preimage_words)]
    fn nullifier_preimage_contract() { preimage_words(kani::any(),kani::any()); }
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::stub_verified(preimage_words)]
    fn nullifier_preimage_owned_equals_words() {
        let key=kani::any::<[u32;8]>().map(M31);
        let salt=kani::any::<[u32;8]>().map(M31);
        let actual=preimage_owned(key,salt);
        let expected=preimage_from_words(key,salt);
        for i in 0..16 { assert_eq!(actual[i],expected[i]); }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::stub(preimage_owned,preimage_from_words)]
    #[kani::stub_verified(preimage_words)]
    fn nullifier_callback_owned_equals_shipped() {
        reset();
        let key = kani::any::<[u32;8]>().map(M31);
        let salt = kani::any::<[u32;8]>().map(M31);
        let actual = derive_nullifier_with(&key, &salt, &mut oracle);
        let expected = derive_nullifier_owned_with(key, salt, |d,x| oracle(d,&x));
        for i in 0..8 { assert_eq!(actual[i],expected[i]); }
        unsafe { let calls=CALLS; let used=USED; assert_eq!(calls,2); assert_eq!(used,1); }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    #[kani::stub(crate::poseidon2::hash_fields, oracle)]
    #[kani::stub(preimage_owned,preimage_from_words)]
    #[kani::stub_verified(preimage_words)]
    fn nullifier_public_owned_equals_shipped() {
        reset();
        let key = kani::any::<[u32;8]>().map(M31);
        let salt = kani::any::<[u32;8]>().map(M31);
        let actual = derive_nullifier(&key,&salt);
        let expected = derive_nullifier_owned(key,salt);
        for i in 0..8 { assert_eq!(actual[i],expected[i]); }
        unsafe { let calls=CALLS; let used=USED; assert_eq!(calls,2); assert_eq!(used,1); }
    }
}
