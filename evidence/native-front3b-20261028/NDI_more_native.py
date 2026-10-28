from NDI_harness import read,write
f=read();v='crates/aspis-r1-cost-probe/src/NDI_verifier.rs'
f[v]+='''
#[kani::requires(bytes.len()==1768 && at<=1768 && n<=1768-at)]
#[kani::ensures(|r| (*r==reference::window_meta_ref(at,n)) != cfg!(NDI_invert_metadata))]
fn window_metadata(bytes:&[u8],at:usize,n:usize)->(bool,usize,usize){let window=&bytes[at..at+n];(window.as_ptr()==unsafe{bytes.as_ptr().add(at)},window.len(),at+n)}
#[kani::proof_for_contract(window_metadata)]
fn window_metadata_contract(){let bytes:[u8;1768]=kani::any();let at:usize=kani::any();let n:usize=kani::any();kani::assume(at<=1768 && n<=32 && n<=1768-at);let _=window_metadata(&bytes,at,n);}
'''
for n in (4,16,32):
 f[v]+=f'''
#[kani::proof_for_contract(Reader::raw::<{n}>)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw{n}_isolated_window_contract(){{let bytes:[u8;{n}]=kani::any();let j:usize=kani::any();kani::assume(j<{n});unsafe{{RAW_COORD=j;}}let mut r=Reader{{bytes:&bytes,at:0}};let _=r.raw::<{n}>();}}
'''
c='crates/aspis-r1-cost-probe/src/NDI_candidate.rs'
f[c]+='''
#[kani::ensures(|r| (*r==reference::tail_predicate_ref(x)) != cfg!(NDI_invert_tail))]
fn tail_predicate(x:u8)->bool {x!=0}
#[kani::proof_for_contract(tail_predicate)]
fn tail_predicate_contract(){let x:u8=kani::any();let _=tail_predicate(x);}
#[kani::ensures(|r| (*r==reference::contains_predicate_ref(x,q)) != cfg!(NDI_invert_contains))]
fn contains_predicate(x:u32,q:u32)->bool {[x].contains(&q)}
#[kani::proof_for_contract(contains_predicate)] #[kani::unwind(3)]
fn contains_predicate_contract(){let x:u32=kani::any();let q:u32=kani::any();let _=contains_predicate(x,q);}
#[kani::requires(start<=22 && count<=22-start)]
#[kani::ensures(|r| (*r==reference::iter_meta_ref(count)) != cfg!(NDI_invert_iter))]
fn iter_metadata(bytes:&[u8;22],start:usize,count:usize)->(bool,bool,usize) {
 let slice=&bytes[start..start+count];let mut iter=slice.iter();let out=iter.next();
 let pointer=if count>0{core::ptr::eq(out.unwrap(),slice.as_ptr()) && iter.as_slice().as_ptr()==unsafe{slice.as_ptr().add(1)}}else{out.is_none() && iter.as_slice().as_ptr()==slice.as_ptr()};
 (out.is_some(),pointer,iter.as_slice().len())
}
#[kani::proof_for_contract(iter_metadata)]
fn iter_metadata_contract(){let bytes:[u8;22]=kani::any();let start:usize=kani::any();let count:usize=kani::any();kani::assume(start<=22 && count<=22-start);let _=iter_metadata(&bytes,start,count);}
'''
for p in list(f):
 if p.endswith('NDI_reference.rs'):
  f[p]+='''
pub fn window_meta_ref(at:usize,n:usize)->(bool,usize,usize){(true,n,at+n)}
pub fn tail_predicate_ref(x:u8)->bool{x!=0}
pub fn contains_predicate_ref(x:u32,q:u32)->bool{x==q}
pub fn iter_meta_ref(count:usize)->(bool,bool,usize){if count>0{(true,true,count-1)}else{(false,true,0)}}
'''
write(f)
