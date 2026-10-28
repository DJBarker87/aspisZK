from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NBF_harness.rs.txt';s=p.read_text()
assert 'fn NBF_query_closure_iteration' not in s
s+='''
static mut NBF_DECODE_PTR:*const u8=core::ptr::null();static mut NBF_DECODE_I:usize=0;static mut NBF_DECODE_OUT:E=E::ZERO;
fn NBF_decode_reply(bytes:&[u8],i:usize)->E {
 unsafe {assert_eq!(bytes.len(),128);NBF_DECODE_PTR=bytes.as_ptr();NBF_DECODE_I=i;let out=NBF_fold_any_e();NBF_DECODE_OUT=out;out}
}
#[kani::proof]
#[kani::unwind(9)]
#[kani::stub(crate::weights::field,NBF_decode_reply)]
fn NBF_query_closure_iteration() {
 let opening:[u8;832]=kani::any();let mut values=[NBF_fold_any_e(),NBF_fold_any_e(),NBF_fold_any_e(),NBF_fold_any_e()];
 let i:usize=kani::any();kani::assume(i<4);let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<8);
 let before=values[j].to_limbs()[k];values[i]=crate::weights::field(&opening[672..800],i);
 unsafe{assert_eq!(NBF_DECODE_PTR,opening.as_ptr().add(672));assert_eq!(NBF_DECODE_I,i);assert_eq!(values[j].to_limbs()[k],if i==j {NBF_DECODE_OUT.to_limbs()[k]} else {before});}
 kani::cover!(i==0);kani::cover!(i==3);kani::cover!(i!=j);
}
fn NBF_compare_cut(folded:E,values:[E;4],u:usize)->Result<E,Error> {
 if folded!=values[u%4] {return Err(Error::Query);}
 Ok(values[u%4])
}
#[kani::proof]
#[kani::unwind(9)]
fn NBF_query_compare_cut() {
 let folded=NBF_fold_any_e();let values=[NBF_fold_any_e(),NBF_fold_any_e(),NBF_fold_any_e(),NBF_fold_any_e()];
 let u:usize=kani::any();kani::assume(u<262144);let k:usize=kani::any();kani::assume(k<8);
 let selected=values[u%4];let result=NBF_compare_cut(folded,values,u);
 if folded!=selected {assert!(matches!(result,Err(Error::Query)));}
 else {assert_eq!(result.unwrap().to_limbs()[k],folded.to_limbs()[k]);}
 kani::cover!(folded==selected);kani::cover!(folded!=selected);
}
#[kani::proof]
#[kani::unwind(9)]
#[kani::stub(aspis_core::field::M31::mul,NBF_field::m31)]
fn NBF_node_native_cut() {
 let z:u32=kani::any();kani::assume(z<2147483647);let z=M31(z);
 let node=z.mul(z).double().sub(M31::ONE);
 unsafe {assert_eq!(NBF_field::MC,1);assert_eq!(NBF_field::MX[0],z.0);assert_eq!(NBF_field::MY[0],z.0);assert_eq!(node,M31(NBF_field::MO[0]).double().sub(M31::ONE));}
 assert!(node.0<2147483647);kani::cover!(z==M31::ZERO);kani::cover!(z.0==2147483646);
}
'''
# Array initialization has no buffer-traversal loop in any of these gates.
array=','.join('NBF_arbitrary_k()' for _ in range(64))
raw=','.join('kani::any::<[u64;4]>()' for _ in range(64))
s+='''
#[kani::proof]
fn NBF_mut_next_prestate() {
 let mut out:[K;64]=['''+array+'''];let ptr=out.as_mut_ptr();
 let i:usize=kani::any();kani::assume(i<=64);
 let mut iter=out[i..].iter_mut();let result=iter.next();
 if i<64 {assert_eq!(result.unwrap() as *mut K,unsafe{ptr.add(i)});assert_eq!(iter.len(),63-i);}
 else {assert!(result.is_none());assert_eq!(iter.len(),0);}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);
}
#[kani::proof]
fn NBF_enumerate_next_prestate() {
 let mut out:[K;64]=['''+array+'''];let ptr=out.as_mut_ptr();let i:usize=kani::any();kani::assume(i<=64);
 let mut iter=out.iter_mut().enumerate();if i>0 {let _=iter.nth(i-1);}
 let result=iter.next();
 if i<64 {let(j,w)=result.unwrap();assert_eq!(j,i);assert_eq!(w as *mut K,unsafe{ptr.add(i)});assert_eq!(iter.len(),63-i);}
 else {assert!(result.is_none());assert_eq!(iter.len(),0);}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);
}
#[kani::proof]
#[kani::unwind(5)]
#[kani::stub(super::BatchedWeights::value,NBF_value_reply)]
fn NBF_enumerate_store_prestate() {
 let mut out:[K;64]=['''+array+'''];let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let q=out[j];let before=[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0][k];
 let backing:Box<[[u64;4]]>=Box::new(['''+raw+''']);let terms:usize=kani::any();let b=BatchedWeights{raw:Vec::from(backing),terms};
 {let mut iter=out.iter_mut().enumerate();if i>0 {let _=iter.nth(i-1);}if let Some((index,w))=iter.next(){*w=b.value(index);}}
 let q=out[j];let after=[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0][k];
 if i<64 {unsafe {assert_eq!(NBF_VALUE_I,i);assert_eq!(after,if i==j {NBF_VALUE_OUT[k]} else {before});}}
 else {assert_eq!(after,before);}
 assert_eq!(b.terms,terms);assert_eq!(b.raw.len(),64);
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}
#[kani::proof]
fn NBF_init_body_prestate() {
 let backing:Box<[[u64;4]]>=Box::new(['''+raw+''']);let mut raw=Vec::from(backing);let weights:[K;64]=['''+array+'''];
 let mut index:usize=kani::any();kani::assume(index<=64);let oldIndex=index;
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);let before=raw[j][k];
 let mut chosen=0;let active=index<weights.len();if active {let w=weights[index];chosen=[w.c0.a.0,w.c0.b.0,w.c1.a.0,w.c1.b.0][k]as u64;raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];index+=1;}
 assert_eq!(index,oldIndex+usize::from(active));assert_eq!(raw[j][k],if active&&j==oldIndex {chosen}else{before});assert_eq!(raw.len(),64);
 kani::cover!(oldIndex==0);kani::cover!(oldIndex==63);kani::cover!(oldIndex==64);
}
'''
s=s.replace('let opening:[u8;832]=kani::any();let mut values=', 'let opening:[u8;832]=['+','.join('kani::any::<u8>()' for _ in range(832))+'];let mut values=')
p.write_text(s)
