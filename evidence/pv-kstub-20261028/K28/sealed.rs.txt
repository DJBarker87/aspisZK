use super::{ArrayLength, Block};
use core::slice;

/// Sealed trait for buffer kinds.
pub trait Sealed {
    /// Invariant guaranteed by a buffer kind, i.e. with correct
    /// buffer code this function always returns true.
    fn invariant(pos: usize, block_size: usize) -> bool;

    /// Split input data into slice of blocks and tail.
    fn split_blocks<N: ArrayLength<u8>>(data: &[u8]) -> (&[Block<N>], &[u8]);
}

impl Sealed for super::Eager {
    #[inline(always)]
    fn invariant(pos: usize, block_size: usize) -> bool {
        pos < block_size
    }

    #[inline(always)]
    fn split_blocks<N: ArrayLength<u8>>(data: &[u8]) -> (&[Block<N>], &[u8]) {
        let nb = data.len() / N::USIZE;
        let blocks_len = nb * N::USIZE;
        let tail_len = data.len() - blocks_len;
        // SAFETY: we guarantee that created slices do not point
        // outside of `data`
        unsafe {
            let blocks_ptr = data.as_ptr() as *const Block<N>;
            let tail_ptr = data.as_ptr().add(blocks_len);
            (
                slice::from_raw_parts(blocks_ptr, nb),
                slice::from_raw_parts(tail_ptr, tail_len),
            )
        }
    }
}

impl Sealed for super::Lazy {
    #[inline(always)]
    fn invariant(pos: usize, block_size: usize) -> bool {
        pos <= block_size
    }

    #[inline(always)]
    fn split_blocks<N: ArrayLength<u8>>(data: &[u8]) -> (&[Block<N>], &[u8]) {
        if data.is_empty() {
            return (&[], &[]);
        }
        let (nb, tail_len) = if data.len() % N::USIZE == 0 {
            (data.len() / N::USIZE - 1, N::USIZE)
        } else {
            let nb = data.len() / N::USIZE;
            (nb, data.len() - nb * N::USIZE)
        };
        let blocks_len = nb * N::USIZE;
        // SAFETY: we guarantee that created slices do not point
        // outside of `data`
        unsafe {
            let blocks_ptr = data.as_ptr() as *const Block<N>;
            let tail_ptr = data.as_ptr().add(blocks_len);
            (
                slice::from_raw_parts(blocks_ptr, nb),
                slice::from_raw_parts(tail_ptr, tail_len),
            )
        }
    }
}

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

#[kani::proof]
#[kani::unwind(132)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn split64_coordinate_lo() {
        let data:[u8;129]=kani::any();let n:usize=kani::any();kani::assume(n<=129);kani::assume(n<=64);
        let b:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(&data[..n]);
        let mut rb=Vec::new();let mut rt=Vec::new();
        reference::split_flat_reference(&data[..n],64,&mut rb,&mut rt);
        assert_eq!(blocks.len()*64,rb.len());assert_eq!(tail.len(),rt.len());
        if b<blocks.len() && j<64 {assert_eq!(blocks[b][j],rb[b*64+j]);}
        assert_eq!(tail.get(k).copied(),rt.get(k).copied());
    }
#[kani::proof]
#[kani::unwind(132)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn split64_coordinate_hi() {
        let data:[u8;129]=kani::any();let n:usize=kani::any();kani::assume(n<=129);kani::assume(n>64);
        let b:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(&data[..n]);
        let mut rb=Vec::new();let mut rt=Vec::new();
        reference::split_flat_reference(&data[..n],64,&mut rb,&mut rt);
        assert_eq!(blocks.len()*64,rb.len());assert_eq!(tail.len(),rt.len());
        if b<blocks.len() && j<64 {assert_eq!(blocks[b][j],rb[b*64+j]);}
        assert_eq!(tail.get(k).copied(),rt.get(k).copied());
    }
#[kani::proof]
#[kani::unwind(132)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn split64_coordinate_lo_negative() {
        let data:[u8;129]=[65;129];let n:usize=63;kani::assume(n<=129);kani::assume(n<=64);
        let b:usize=0;let j:usize=0;let k:usize=0;
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(&data[..n]);
        let mut rb=Vec::new();let mut rt=Vec::new();
        reference::split_flat_reference(&data[..n],64,&mut rb,&mut rt);
        assert_eq!(blocks.len()*64,rb.len());assert_eq!(tail.len(),rt.len());
        if b<blocks.len() && j<64 {assert_eq!(blocks[b][j],rb[b*64+j]);}
        assert_ne!(tail.get(k).copied(),rt.get(k).copied());
    }
#[kani::proof]
#[kani::unwind(132)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn split64_coordinate_hi_negative() {
        let data:[u8;129]=[65;129];let n:usize=65;kani::assume(n<=129);kani::assume(n>64);
        let b:usize=0;let j:usize=0;let k:usize=0;
        let (blocks,tail)=<crate::Eager as Sealed>::split_blocks::<generic_array::typenum::U64>(&data[..n]);
        let mut rb=Vec::new();let mut rt=Vec::new();
        reference::split_flat_reference(&data[..n],64,&mut rb,&mut rt);
        assert_eq!(blocks.len()*64,rb.len());assert_eq!(tail.len(),rt.len());
        if b<blocks.len() && j<64 {assert_eq!(blocks[b][j],rb[b*64+j]);}
        assert_ne!(tail.get(k).copied(),rt.get(k).copied());
    }}
