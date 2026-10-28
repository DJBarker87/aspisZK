from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/verifier.rs'
t='\n#[cfg(kani)] mod NCB_geometry_steps {\nuse super::*;\n'
for mode in ['value','cursor','geometry']:
 t+='#[kani::proof] #[kani::unwind(64)]\n'+attrs+f'fn query_{mode}()'+'{\n'
 t+='''let queries:[u32;22]=kani::any();let start:usize=kani::any();let current:usize=kani::any();let end:usize=kani::any();kani::assume(start<=current&&current<end&&end<=22);
 let mut iter=queries[current..end].iter();let reference=iter.next().unwrap();let query=*reference;
 '''+{'value':'assert!(query==queries[current]);assert!(core::ptr::eq(reference,&queries[current]));','cursor':'assert!(iter.as_slice().len()==end-current-1);assert!(core::ptr::eq(iter.as_slice().as_ptr(),queries[current+1..end].as_ptr()));','geometry':'let rows=current-start;assert!(rows<22&&(rows+1)*5<=110);assert!((current+1)-start==rows+1);'}[mode]+'\n}\n'
t+='''#[kani::proof] #[kani::unwind(4)] fn query_end(){let queries:[u32;22]=kani::any();let end:usize=kani::any();kani::assume(end<=22);let mut it=queries[end..end].iter();assert!(it.next()==None);assert!(it.as_slice().is_empty());}
 #[kani::proof] #[kani::unwind(4)] fn reverse_active(){let remaining:usize=kani::any();kani::assume(remaining>0&&remaining<=110);let mut it=(0usize..remaining).rev();assert!(it.next()==Some(remaining-1));assert!(it.size_hint()==(remaining-1,Some(remaining-1)));}
 #[kani::proof] #[kani::unwind(4)] fn reverse_done(){let mut it=(0usize..0).rev();assert!(it.next()==None);assert!(it.size_hint()==(0,Some(0)));}
 #[kani::proof] #[kani::unwind(4)] fn row_group(){let rows:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(rows<=22&&i<rows&&j<5);let at=5*i+j;assert!(at<5*rows&&at<110);}
}\n'''
emit(p,t,'NCB_geometry_steps')
