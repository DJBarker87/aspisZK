#![allow(dead_code)]
#[path="../../../programs/r1-cost-probe/src/pool_route.rs"]
mod route;
include!("source-cuts.rs");

#[cfg(kani)]
mod proofs {
    use super::*;
    const C:usize=POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    const N:usize=C+verifier::PROOF_BYTES;

    #[kani::proof]
    #[kani::unwind(70)]
    fn admitted_route_and_no_lifecycle() {
        let bytes:[u8;64]=kani::any();
        let n:usize=kani::any();kani::assume(n<=64);
        let data=&bytes[..n];let ok=route::admitted(data);
        assert_eq!(ok,(n==2 && bytes[0]==3 && (bytes[1]==10||bytes[1]==11)) ||
            (n>=4 && bytes[0]==b'A'&&bytes[1]==b'S'&&bytes[2]==b'Q'&&bytes[3]==b'8'));
        if n>0 && (bytes[0]==4||bytes[0]==5||bytes[0]==6) { assert!(!ok); }
    }
    #[kani::proof]
    fn readonly_exact() {
        let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();
        assert_eq!(readonly_buffer_meta_ok(s,w,e).is_ok(),!s&&!w&&!e);
    }
    #[kani::proof]
    #[kani::unwind(700)]
    fn stage1_exact_slice() {
        let bytes:[u8;N]=kani::any();
        let n:usize=kani::any();kani::assume(n<=N);
        let input=&bytes[..n];
        // The caller's encoded candidate is held equal to this prefix for
        // the successful slice theorem; its source encoding is a different cone.
        let candidate:[u8;C]=bytes[..C].try_into().unwrap();
        match stage1_slice(input,candidate) {
          Ok(proof)=>{
            assert_eq!(n,N);assert_eq!(proof.len(),verifier::PROOF_BYTES);
            assert_eq!(proof.as_ptr(),input[C..].as_ptr());
            assert_eq!(bytes[C+8],Variant::S2.tag());
          },
          Err(_)=>assert!(n!=N || bytes[C+8]!=Variant::S2.tag()),
        }
        assert_eq!(C,688);assert_eq!(verifier::PROOF_BYTES,57607);
    }
    #[kani::proof]
    fn stage2_exact_slice() {
        let bytes:[u8;N]=kani::any();
        let n:usize=kani::any();kani::assume(n<=N);
        // validate_asq8 obtains PROOF_BYTES from scan_proof_buffer.
        let input=&bytes[..n];
        match stage2_slice(input,ValidatedAsqa{proof_length:verifier::PROOF_BYTES}) {
          Ok(proof)=>{
            assert_eq!(n,N);assert_eq!(proof.len(),verifier::PROOF_BYTES);
            assert_eq!(proof.as_ptr(),input[C..].as_ptr());
          },
          Err(_)=>assert_ne!(n,N),
        }
    }
}
