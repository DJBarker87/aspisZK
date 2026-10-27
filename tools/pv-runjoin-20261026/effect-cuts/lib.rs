fn entropy_nonzero32(bytes:&[u8;32])->bool {
    let mut combined=0u8;let mut i=0;
    while i<32 {combined|=bytes[i];i+=1;}
    combined!=0
}

#[cfg(kani)]
mod checks {
    use super::*;
    #[kani::proof] #[kani::unwind(34)]
    fn scan_exact() {
        let a: [u8;32]=kani::any();
        let mut expected=false;
        for i in 0..32 {expected |= a[i]!=0;}
        assert_eq!(entropy_nonzero32(&a),expected);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_zero_iff() {
        let a: [u8;32]=kani::any();
        assert_eq!(!entropy_nonzero32(&a),a==[0;32]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_reverse() {
        let a: [u8;32]=kani::any();let mut b=[0;32];
        for i in 0..32 {b[31-i]=a[i];}
        assert_eq!(entropy_nonzero32(&a),entropy_nonzero32(&b));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_rotate() {
        let a: [u8;32]=kani::any();let mut b=[0;32];
        let shift:usize=kani::any();kani::assume(shift<32);
        for i in 0..32 {b[(i+shift)%32]=a[i];}
        assert_eq!(entropy_nonzero32(&a),entropy_nonzero32(&b));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_witness() {
        let a: [u8;32]=kani::any();let i:usize=kani::any();
        kani::assume(i<32 && a[i]!=0);
        assert!(entropy_nonzero32(&a));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn single_byte() {
        let mut a=[0;32];let i:usize=kani::any();let b:u8=kani::any();
        kani::assume(i<32);a[i]=b;
        assert_eq!(entropy_nonzero32(&a),b!=0);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split_roundtrip() {
        let raw:[u8;64]=kani::any();let mut left=[0;32];let mut right=[0;32];
        left.copy_from_slice(&raw[..32]);right.copy_from_slice(&raw[32..]);
        let mut joined=[0;64];joined[..32].copy_from_slice(&left);joined[32..].copy_from_slice(&right);
        assert_eq!(raw,joined);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn split_left() {
        let raw:[u8;64]=kani::any();let mut left=[0;32];
        left.copy_from_slice(&raw[..32]);
        let i:usize=kani::any();kani::assume(i<32);
        assert_eq!(left[i],raw[i]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn split_right() {
        let raw:[u8;64]=kani::any();let mut right=[0;32];
        right.copy_from_slice(&raw[32..]);
        let i:usize=kani::any();kani::assume(i<32);
        assert_eq!(right[i],raw[i+32]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn acceptance_exact() {
        let raw:[u8;64]=kani::any();let mut left=[0;32];let mut right=[0;32];
        left.copy_from_slice(&raw[..32]);right.copy_from_slice(&raw[32..]);
        assert_eq!(entropy_nonzero32(&left)&&entropy_nonzero32(&right),
            left!=[0;32]&&right!=[0;32]);
    }
}
