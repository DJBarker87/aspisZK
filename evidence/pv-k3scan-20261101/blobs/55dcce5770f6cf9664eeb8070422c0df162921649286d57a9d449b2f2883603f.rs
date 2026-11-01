//! Parametric oracle-call contracts, without a SHA-256 or privacy claim.
use core::cell::Cell;
use aspis_core::Digest32;
#[derive(Clone,Copy)]
struct Checked<'a> {header:[u8;2],header_len:usize,left:&'a[u8],right:&'a[u8],answer:[u8;32],calls:&'a Cell<u8>}
impl Digest32 for Checked<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        assert_eq!(self.calls.get(),0);self.calls.set(1);
        assert_eq!(parts.len(),3);
        assert_eq!(parts[0],&self.header[..self.header_len]);
        assert_eq!(parts[1].len(),self.left.len());
        assert_eq!(parts[1].as_ptr(),self.left.as_ptr());
        assert_eq!(parts[2].len(),self.right.len());
        assert_eq!(parts[2].as_ptr(),self.right.as_ptr());
        self.answer
    }
}
#[kani::proof]
#[kani::unwind(36)]
fn private_leaf_framing() {
    let value:[u8;480]=kani::any();let salt:[u8;32]=kani::any();let tag:u8=kani::any();
    let answer:[u8;32]=kani::any();let n=if kani::any() {128} else {480};
    let calls=Cell::new(0);
    let h=Checked{header:[0x10,tag],header_len:2,left:&value[..n],right:&salt,answer,calls:&calls};
    assert_eq!(aspis_core::state_only_private_merkle::private_leaf_hash_with_digest(h,tag,&value[..n],&salt),answer);
    assert_eq!(calls.get(),1);
}
#[kani::proof]
#[kani::unwind(36)]
fn binary_parent_framing() {
    let left:[u8;32]=kani::any();let right:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
    let calls=Cell::new(0);
    let h=Checked{header:[0x12,0],header_len:1,left:&left,right:&right,answer,calls:&calls};
    assert_eq!(super::multiproof::binary_parent(h,&left,&right),answer);
    assert_eq!(calls.get(),1);
}
