//! P6 key projection of the original unique-account prefix. Native coupling separate.
pub fn key_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len()!=b.len(){return false;}
    let mut i=0;let mut equal=true;
    while i<a.len() && equal {let x=a[i];let y=b[i];equal=x==y;i+=1;}
    equal
}
pub fn right_unique(keys: &[[u8;32]], left: usize) -> bool {
    let mut right=left+1;let mut unique=true;
    while right<keys.len() && unique {
        let a=keys[left];let b=keys[right];
        unique=!key_equal(&a,&b);
        right+=1;
    }
    unique
}
pub fn unique_keys(keys: &[[u8;32]]) -> bool {
    let mut left=0;let mut unique=true;
    while left<keys.len() && unique {
        unique=right_unique(keys,left);
        left+=1;
    }
    unique
}
