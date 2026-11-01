
#[cfg(kani)]
mod pv_cblib_library_checks {
    extern crate std;
    use self::std::vec::Vec;
    use super::*;
    fn reference(data: &[u8], size: usize) -> (Vec<Vec<u8>>,Vec<u8>) {
        let count=data.len()/size;
        let mut blocks=Vec::new();let mut i=0;
        while i<count {
            let mut block=Vec::new();let mut j=0;
            while j<size {block.push(data[i*size+j]);j+=1;}
            blocks.push(block);i+=1;
        }
        let mut tail=Vec::new();let mut k=count*size;
        while k<data.len() {tail.push(data[k]);k+=1;}
        (blocks,tail)
    }
    #[kani::proof]
    #[kani::unwind(132)]
    fn op209_split64() {
        let data:[u8;128]=kani::any();let n:usize=kani::any();kani::assume(n<=128);
        let b:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(&data[..n]);
        let (rb,rt)=reference(&data[..n],64);
        assert_eq!(blocks.len(),rb.len());assert_eq!(tail.len(),rt.len());
        assert_eq!(blocks.get(b).and_then(|x|x.get(j)).copied(),rb.get(b).and_then(|x|x.get(j)).copied());
        assert_eq!(tail.get(k).copied(),rt.get(k).copied());
    }
}
