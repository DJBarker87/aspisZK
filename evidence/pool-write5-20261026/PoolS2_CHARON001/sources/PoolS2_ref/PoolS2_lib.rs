//! P6 key projection of the original unique-account prefix. Native coupling separate.
pub fn key_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len()!=b.len(){return false;}
    let mut i=0;
    while i<a.len(){let x=a[i];let y=b[i];if x!=y{return false;}i+=1;}
    true
}
pub fn unique_keys(keys: &[[u8;32]]) -> bool {
    let mut left=0;
    while left<keys.len(){
        let mut right=left+1;
        while right<keys.len(){
            let a=keys[left];let b=keys[right];
            if key_equal(&a,&b){return false;}
            right+=1;
        }
        left+=1;
    }
    true
}
