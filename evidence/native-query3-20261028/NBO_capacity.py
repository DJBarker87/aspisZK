from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NBO_native.rs.txt').read_text()
rows=','.join('kani::any::<[u64;4]>()' for _ in range(64))
s+='''
// Capacity is arbitrary throughout the native allocation layout domain.
// This checks one indexed slice setter, never the query or row loop.
#[kani::proof]
#[kani::unwind(4096)]
fn NBO_capacity_row() {
 let cap:usize=kani::any();kani::assume(cap>=64);kani::assume(cap<=isize::MAX as usize/core::mem::size_of::<[u64;4]>());
 let initial:[[u64;4];64]=['''+rows+'''];
 let mut raw:Vec<[u64;4]>=Vec::with_capacity(cap);raw.extend_from_slice(&initial);
 assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);let ptr=raw.as_ptr();
 let i:usize=kani::any();kani::assume(i<64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let new:[u64;4]=kani::any();let before=raw[j][k];
 raw[i]=new;
 assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);assert_eq!(raw.as_ptr(),ptr);
 assert_eq!(raw[j][k],if i==j {new[k]}else{before});
 kani::cover!(cap==64);kani::cover!(cap>64);kani::cover!(i!=j);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
