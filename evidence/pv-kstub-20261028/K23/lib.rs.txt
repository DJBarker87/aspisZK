#![feature(allocator_api)]
extern crate alloc;
#[path="/home/dombarker/project-offloads/codex-pv-kstub-20261028/KMX_stubs.rs"] pub mod KMX_stubs;
use aspis_core::field::{QM31,CM31,M31};
fn q(w:[u32;4])->QM31 {
        QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}
    }
fn wide_bytes_flat(x:aspis_core::field::WideExact)->[u8;32] {
 let l=x.to_limbs();let a=l[0].to_le_bytes();let b=l[1].to_le_bytes();let c=l[2].to_le_bytes();let d=l[3].to_le_bytes();
 let e=l[4].to_le_bytes();let f=l[5].to_le_bytes();let g=l[6].to_le_bytes();let h=l[7].to_le_bytes();
 [a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]
}
#[kani::proof]
#[kani::unwind(65)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn wide_flat() {
        let raw:[u32;8]=kani::any();
        let x=aspis_core::field::WideExact::new(q([raw[0],raw[1],raw[2],raw[3]]),q([raw[4],raw[5],raw[6],raw[7]]));
        assert_eq!(x.to_le_bytes(),wide_bytes_flat(x));
    }
#[kani::proof]
#[kani::unwind(65)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::KMX_stubs::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn wide_flat_negative() {
        let raw:[u32;8]=[0x01020304;8];
        let x=aspis_core::field::WideExact::new(q([raw[0],raw[1],raw[2],raw[3]]),q([raw[4],raw[5],raw[6],raw[7]]));
        assert_ne!(x.to_le_bytes(),wide_bytes_flat(x));
    }