//! Actual HashFn compatibility path, including LegacyHashFn delegation.
static mut CALLS:usize=0;
static mut TAG:u8=0;
static mut VALUE:*const u8=core::ptr::null();
static mut LENGTH:usize=0;
static mut SALT:*const u8=core::ptr::null();
static mut ANSWER:[u8;32]=[0;32];
fn check_hash(parts:&[&[u8]])->[u8;32] {
    assert_eq!(unsafe{CALLS},0);unsafe{CALLS=1;}
    assert_eq!(parts.len(),3);assert_eq!(parts[0],&[0x10,unsafe{TAG}]);
    assert_eq!(parts[1].as_ptr(),unsafe{VALUE});assert_eq!(parts[1].len(),unsafe{LENGTH});
    assert_eq!(parts[2].as_ptr(),unsafe{SALT});assert_eq!(parts[2].len(),32);
    unsafe{ANSWER}
}
#[kani::proof]
#[kani::unwind(36)]
fn private_hash_fn_frame() {
    let value:[u8;480]=kani::any();let salt:[u8;32]=kani::any();
    let tag:u8=kani::any();let answer:[u8;32]=kani::any();let n=if kani::any() {128} else {480};
    unsafe{CALLS=0;TAG=tag;VALUE=value.as_ptr();LENGTH=n;SALT=salt.as_ptr();ANSWER=answer;}
    let out=aspis_core::state_only_private_merkle::private_leaf_hash(check_hash,tag,&value[..n],&salt);
    assert_eq!(out,answer);assert_eq!(unsafe{CALLS},1);
}

fn check_plain_hash(parts:&[&[u8]])->[u8;32] {
    assert_eq!(unsafe{CALLS},0);unsafe{CALLS=1;}
    assert_eq!(parts.len(),2);assert_eq!(parts[0],&[0x10,unsafe{TAG}]);
    assert_eq!(parts[1].as_ptr(),unsafe{VALUE});assert_eq!(parts[1].len(),unsafe{LENGTH});
    unsafe{ANSWER}
}
#[kani::proof]
#[kani::unwind(36)]
fn plain_hash_fn_frame() {
    let value:[u8;480]=kani::any();let tag:u8=kani::any();let answer:[u8;32]=kani::any();
    let n:usize=kani::any();kani::assume(n<=480);
    unsafe{CALLS=0;TAG=tag;VALUE=value.as_ptr();LENGTH=n;ANSWER=answer;}
    let out=aspis_core::r0::merkle::leaf(check_plain_hash,tag,&value[..n]);
    assert_eq!(out,answer);assert_eq!(unsafe{CALLS},1);
}
