//! Direct selected 64-byte factory contracts; OS filling is the E1 boundary.
use super::*;
static mut CALLS:usize=0;
static mut FIELD:[u8;32]=[0;32];
static mut LEAF:[u8;32]=[0;32];
fn model_nonzero32(bytes:&[u8;32])->bool {
    let a=u64::from_le_bytes([bytes[0],bytes[1],bytes[2],bytes[3],bytes[4],bytes[5],bytes[6],bytes[7]]);
    let b=u64::from_le_bytes([bytes[8],bytes[9],bytes[10],bytes[11],bytes[12],bytes[13],bytes[14],bytes[15]]);
    let c=u64::from_le_bytes([bytes[16],bytes[17],bytes[18],bytes[19],bytes[20],bytes[21],bytes[22],bytes[23]]);
    let d=u64::from_le_bytes([bytes[24],bytes[25],bytes[26],bytes[27],bytes[28],bytes[29],bytes[30],bytes[31]]);
    (a|b|c|d)!=0
}
#[kani::proof]
#[kani::unwind(40)]
fn zero32_kernel_contract() {
    let bytes:[u8;32]=kani::any();let expected=bytes!=[0;32];
    assert_eq!(super::entropy_nonzero32(&bytes),expected);
    assert_eq!(model_nonzero32(&bytes),expected);
}
fn supplied_fill(bytes:&mut[u8])->Result<(),getrandom::Error> {
    assert_eq!(bytes.len(),64);unsafe{CALLS+=1;}
    bytes[..32].copy_from_slice(&unsafe{FIELD});
    bytes[32..].copy_from_slice(&unsafe{LEAF});
    Ok(())
}
fn failed_fill(bytes:&mut[u8])->Result<(),getrandom::Error> {
    assert_eq!(bytes.len(),64);unsafe{CALLS+=1;}
    Err(getrandom::Error::UNSUPPORTED)
}
#[kani::proof]
#[kani::unwind(80)]
#[kani::stub(super::entropy_nonzero32,model_nonzero32)]
#[kani::stub(getrandom::fill,supplied_fill)]
fn factory64_success_and_zero_nonce() {
    let nonce:[u8;32]=kani::any();let field:[u8;32]=kani::any();let leaf:[u8;32]=kani::any();
    kani::assume(field!=[0;32] && leaf!=[0;32]);
    unsafe{CALLS=0;FIELD=field;LEAF=leaf;}
    let result=StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce);
    if nonce==[0;32] {
        assert!(matches!(result,Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
        assert_eq!(unsafe{CALLS},0);
    } else {
        let attempt=result.unwrap();
        assert_eq!(attempt.mask_nonce,nonce);assert_eq!(*attempt.field_mask_entropy,field);assert_eq!(*attempt.leaf_salt_seed,leaf);
        assert_eq!(unsafe{CALLS},1);
    }
}
#[kani::proof]
#[kani::unwind(80)]
#[kani::stub(super::entropy_nonzero32,model_nonzero32)]
#[kani::stub(getrandom::fill,supplied_fill)]
fn factory64_zero_seed_exhaustion() {
    let nonce:[u8;32]=kani::any();let field:[u8;32]=kani::any();let leaf:[u8;32]=kani::any();
    kani::assume(nonce!=[0;32]);kani::assume(field==[0;32] || leaf==[0;32]);
    unsafe{CALLS=0;FIELD=field;LEAF=leaf;}
    let result=StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce);
    assert!(matches!(result,Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
    assert_eq!(unsafe{CALLS},ENTROPY_RETRY_LIMIT);
}
#[kani::proof]
#[kani::unwind(80)]
#[kani::stub(super::entropy_nonzero32,model_nonzero32)]
#[kani::stub(getrandom::fill,failed_fill)]
fn factory64_os_error() {
    let nonce:[u8;32]=kani::any();kani::assume(nonce!=[0;32]);unsafe{CALLS=0;}
    assert!(matches!(StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce),Err(StateOnlyAttemptEntropyError::Os(_))));
    assert_eq!(unsafe{CALLS},1);
}
