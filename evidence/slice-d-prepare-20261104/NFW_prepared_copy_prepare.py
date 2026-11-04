from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NFW_prepared_native_prepare.py';s=p.read_text()
code='''
#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_q(){let src=qs::<10>();let mut dst=[K::ZERO;10];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),10);}let i:usize=kani::any();kani::assume(i<10);assert!((src[i]==dst[i])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_point(){let src=[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}];let mut dst=[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),2);}let i:usize=kani::any();kani::assume(i<2);assert!((src[i]==dst[i])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_queries(){let src:[u32;22]=kani::any();let mut dst=[0u32;22];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),22);}let i:usize=kani::any();kani::assume(i<22);assert!((src[i]==dst[i])!=cfg!(NFW_invert));}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn copy_folded_wrong(){let mut root=[0u8;32];root[31]=17;let mut tail=[0u8;224];tail[223]=128;let mut dst=Vec::with_capacity(256);dst.extend_from_slice(&root);dst.extend_from_slice(&tail);assert_eq!(dst[255],0);}
'''
pos=s.index('# A new child module');s=s[:pos]+'code+='+repr(code)+'\n'+s[pos:];p.write_text(s)
