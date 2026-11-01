
// Proof-only append. The original sealed.rs prefix is byte-pinned unchanged.
#[cfg(any(kani,test))]
mod pv_alib_checks {
    extern crate std;
    use self::std::vec::Vec;
    use super::*;
    #[path="/home/dombarker/project-offloads/codex-pv-alib-20261027/split-flat-reference.rs"]
    mod reference;
    fn compare(data:&[u8]) {
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(data);
        let mut rb=Vec::new();let mut rt=Vec::new();
        reference::split_flat_reference(data,64,&mut rb,&mut rt);
        assert_eq!(blocks.len()*64,rb.len());assert_eq!(tail,rt);
        for (i,b) in blocks.iter().enumerate() {assert_eq!(&b[..],&rb[i*64..(i+1)*64]);}
    }
    #[test]
    fn split_native_differential() {
        let data:Vec<u8>=(0..1025).map(|i|((i*17+29)%256)as u8).collect();
        for n in 0..=data.len() {compare(&data[..n]);}
        std::println!("1026 arbitrary-length-prefix native comparisons passed, no SHA-NI claim");
    }
    #[cfg(kani)]
    #[kani::proof]
    #[kani::unwind(132)]
    fn split64_coordinate() {
        let data:[u8;129]=kani::any();let n:usize=kani::any();kani::assume(n<=129);
        let b:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(&data[..n]);
        let mut rb=Vec::new();let mut rt=Vec::new();
        reference::split_flat_reference(&data[..n],64,&mut rb,&mut rt);
        assert_eq!(blocks.len()*64,rb.len());assert_eq!(tail.len(),rt.len());
        if b<blocks.len() && j<64 {assert_eq!(blocks[b][j],rb[b*64+j]);}
        assert_eq!(tail.get(k).copied(),rt.get(k).copied());
    }
}
