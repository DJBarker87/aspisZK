#[cfg(test)]
mod SDY_fidelity {
    extern crate std;
    use super::*;
    #[test]
    fn SDY_sampler() {
        for (mut digits,addend,expected,carry) in [
            ([0u32;8],1u32,[1,0,0,0,0,0,0,0],false),
            ([2147483646u32;8],1,[0u32;8],true),
            ([5u32;8],2147483647,[5,6,5,5,5,5,5,5],false),
        ] {let old=digits;let actual=add_small_base_p(&mut digits,addend);std::println!("SDY add {:?} {} => {:?} {}",old,addend,digits,actual);assert_eq!((digits,actual),(expected,carry));}
    }
}
