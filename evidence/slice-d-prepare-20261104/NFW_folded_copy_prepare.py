from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NFW_prepared_native_prepare.py';s=p.read_text()
assert 'fn copy_folded(){' not in s
code='''
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn copy_folded(){let root:[u8;32]=kani::any();let tail:[u8;224]=kani::any();let mut dst=Vec::with_capacity(256);dst.extend_from_slice(&root);dst.extend_from_slice(&tail);let at:usize=kani::any();kani::assume(at<256);let expected=if at<32{root[at]}else{tail[at-32]};assert_eq!(dst[at],expected);}
'''
pos=s.index('# A new child module');s=s[:pos]+'code+='+repr(code)+'\n'+s[pos:];p.write_text(s)
