from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/fast_dots.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
read=frozen.split('                let scalar = ',1)[1].split('                sums[0]',1)[0]
read='let scalar = '+read
(E/'NCB_DOT_READ_SOURCE.json').write_text(__import__('json').dumps({'source':p,'revision':'4bb3b3f5','source_window':read,'sha256':hashlib.sha256(read.encode()).hexdigest(),'meaning':'exact scalar and coefficient reads; one actual Range::next before the source body'},indent=2)+'\n')
t='\n#[cfg(kani)] mod NCB_dotcuts {\nuse super::*;\nfn word(q:&[u8;608],at:usize)->u32{u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])}\n'
for mode in ['iterator','scalar','coefficient']:
 t+='#[kani::proof] #[kani::unwind(512)]\n'+attrs+f'fn inner_{mode}()'+'{\n'
 t+='''let q:[u8;608]=kani::any();let raw:[[u32;8];29]=kani::any();let g:[WideExact;29]=unsafe{core::mem::transmute(raw)};
 let slot:usize=kani::any();kani::assume(slot<4);let start:usize=kani::any();let end:usize=kani::any();kani::assume(start<end&&end<=26);
 let at=slot*120+start*4;let expected=word(&q,at);kani::assume(expected<2147483647);
 let want=g[start].to_limbs();let mut iter=start..end;
 let term=iter.next().unwrap();
 '''+read+'\n'
 t+= {'iterator':'assert!(term==start&&iter.start==start+1&&iter.end==end);','scalar':'assert!(scalar.0==expected&&scalar.0<2147483647);','coefficient':'let j:usize=kani::any();kani::assume(j<8);assert!(coefficient[j]==want[j]);'}[mode]+'\n}\n'
t+='''#[kani::proof] #[kani::unwind(4)] fn inner_stopped(){let start:usize=kani::any();let end:usize=kani::any();kani::assume(end<=26&&start>=end);let mut it=start..end;assert!(it.next()==None);assert!(it.start==start&&it.end==end);}
 #[kani::proof] #[kani::unwind(4)] fn outer_initial(){let mut it=(0usize..26).step_by(4);assert!(it.next()==Some(0));assert!(it.size_hint()==(6,Some(6)));}
 #[kani::proof] #[kani::unwind(4)] fn outer_next(){let n:usize=kani::any();kani::assume(n<6);let start=4*n;let mut it=(start..26).step_by(4);assert!(it.next()==Some(start));assert!(it.next()==Some(start+4));assert!(it.size_hint()==(5-n,Some(5-n)));}
 #[kani::proof] #[kani::unwind(4)] fn outer_last(){let mut it=(24usize..26).step_by(4);assert!(it.next()==Some(24));assert!(it.next()==None);assert!(it.size_hint()==(0,Some(0)));}
}\n'''
emit(p,t,'NCB_dotcuts')
