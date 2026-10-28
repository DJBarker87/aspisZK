from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_tail.rs').read_text()
s=s.replace('[[u32;4];2]=[[0;4];2]','[[u32;4];6]=[[0;4];6]').replace('[[u64;4];2]=[[0;4];2]','[[u64;4];6]=[[0;4];6]').replace('assert!(i<2);','assert!(i<6);')
s+='''
static mut NCG_RC:usize=0;static mut NCG_RI:[u64;8]=[0;8];static mut NCG_RO:[u32;8]=[0;8];
fn NCG_reduce(x:u64)->u32{let z:u32=kani::any();kani::assume(z<P);unsafe{let i=NCG_RC;assert!(i<8);NCG_RI[i]=x;NCG_RO[i]=z;NCG_RC+=1;}z}
fn NCG_finish_case(add_base:bool,negative:bool){
 let old0:[u64;4]=kani::any();let old1:[u64;4]=kani::any();let count:usize=kani::any();let state=EbyKDot{c0:Dot{sums:old0},c1:Dot{sums:old1},count};
 let bw:[u32;8]=kani::any();for w in bw{kani::assume(w<P);}let base=E::from_limbs(bw).unwrap();let k:usize=kani::any();kani::assume(k<8);
 let tail=state.finish();let out=if add_base{base.add(tail)}else{tail};
 unsafe{assert_eq!(NCG_RC,8);let expected_input=if k<4{old0[k]}else{old1[k-4]};assert_eq!(NCG_RI[k],expected_input);
 let reply=E::from_limbs(NCG_RO).unwrap();let expected=if add_base{base.add(reply)}else{reply};
 if negative{assert_ne!(out.to_limbs()[k],expected.to_limbs()[k]);}else{assert_eq!(out.to_limbs()[k],expected.to_limbs()[k]);}}
 kani::cover!(k==7&&count==usize::MAX);
}
fn NCG_three_push_case(negative:bool){
 let v0:[u32;8]=kani::any();let v1:[u32;8]=kani::any();let v2:[u32;8]=kani::any();for w in v0{kani::assume(w<P);}for w in v1{kani::assume(w<P);}for w in v2{kani::assume(w<P);}
 let coeff=[E::from_limbs(v0).unwrap(),E::from_limbs(v1).unwrap(),E::from_limbs(v2).unwrap()];
 let s0:[u32;4]=kani::any();let s1:[u32;4]=kani::any();let s2:[u32;4]=kani::any();for w in s0{kani::assume(w<P);}for w in s1{kani::assume(w<P);}for w in s2{kani::assume(w<P);}
 let mut tail=EbyKDot::new();tail.push(coeff[0],NCG_q(s0)).unwrap();tail.push(coeff[1],NCG_q(s1)).unwrap();tail.push(coeff[2],NCG_q(s2)).unwrap();
 let step:usize=kani::any();let half:usize=kani::any();let k:usize=kani::any();kani::assume(step<3&&half<2&&k<4);
 unsafe{assert_eq!(NCG_CALLS,6);assert_eq!(tail.count,3);assert_eq!(NCG_X[2*step+half][k],coeff[step].to_limbs()[4*half+k]);assert_eq!(NCG_Y[2*step+half][k],[s0,s1,s2][step][k]);
 let fold=|v:u64|(v&u64::from(P)).wrapping_add(v>>31);
 let expected=fold(NCG_O[half][k]).wrapping_add(fold(NCG_O[2+half][k])).wrapping_add(fold(NCG_O[4+half][k]));
 let actual=if half==0{tail.c0.sums[k]}else{tail.c1.sums[k]};if negative{assert_ne!(actual,expected);}else{assert_eq!(actual,expected);}}
 kani::cover!(step==2&&half==1&&k==3);
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
for typ,call,stub in [('finish','NCG_finish_case(false,NEG)','#[kani::stub(super::reduce,NCG_reduce)]\n'),('finish_add','NCG_finish_case(true,NEG)','#[kani::stub(super::reduce,NCG_reduce)]\n'),('three_push','NCG_three_push_case(NEG)','#[kani::stub(super::Q::raw,NCG_raw)]\n')]:
 for neg in [False,True]:s+=attrs+stub+'fn NCG_'+typ+('_negative' if neg else '')+'(){'+call.replace('NEG',str(neg).lower())+';}\n'
Path('/tmp/NCG_tail_finish.rs').write_text(s)
(E/'NCG_tail_finish.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_tail.rs')))
# Two base-log fidelity controls, same configuration and same source inputs.
n=Path('/tmp/NCG_coefficients.rs').read_text()
for neg in [False,True]:n+=attrs+'#[kani::stub(NCG_add_expression,NCG_add_spec)]\nfn NCG_log_index'+('_negative' if neg else '')+'(){NCG_postread_case(true,false);unsafe{assert_eq!(NCG_OUT[0],NCG_OUT['+('1' if neg else '0')+']);}}\n'
Path('/tmp/NCG_last_native.rs').write_text(n)
(E/'NCG_last_native.patch').write_text(''.join(difflib.unified_diff([],n.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
