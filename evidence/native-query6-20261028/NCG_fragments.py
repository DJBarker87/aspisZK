from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_native.rs').read_text()
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
s+='''
// Post-read split: NBZ paired decoder/coefficient gates supply these scalar inputs.
fn NCG_postread_case(eight:bool,negative:bool){
 let mut sums:[u64;8]=kani::any();let old=sums;
 let c:[u32;8]=kani::any();let scalar:u32=kani::any();let phase:usize=kani::any();
 let k:usize=kani::any();let j:usize=kani::any();kani::assume(k<8&&j<8&&phase<4);
 kani::assume(scalar<2147483647);for x in c{kani::assume(x<2147483647);}
 for x in sums{kani::assume(x<(1u64<<34)+(phase as u64)*NCG_D);}
 unsafe{NCG_PHASE=phase;}
 if eight {
'''
for k in range(8):s+=f'sums[{k}]=NCG_add_expression(sums[{k}],c[{k}],scalar);\n'
s+='''
 } else {sums[k]=NCG_add_expression(sums[k],c[k],scalar);}
 unsafe{
 let n=if eight{8}else{1};assert_eq!(NCG_CALLS,n);
 let index=if eight{k}else{0};
 assert_eq!(NCG_OLD[index],old[k]);assert_eq!(NCG_COEFF[index],c[k]);assert_eq!(NCG_SCALAR[index],scalar);
 let expected=if eight||j==k {NCG_OUT[if eight{j}else{0}]}else{old[j]};
 if negative{assert_ne!(sums[j],expected);}else{assert_eq!(sums[j],expected);}
 }
 kani::cover!(k==7&&j==0&&phase==3);kani::cover!(j==k);
}
static mut NCG_WCALLS:usize=0;
static mut NCG_WX:[[u32;8];4]=[[0;8];4];static mut NCG_WY:[[u32;8];4]=[[0;8];4];static mut NCG_WO:[[u32;8];4]=[[0;8];4];
fn NCG_wide_opaque(x:E,y:E)->E{
 let a=x.to_limbs();let b=y.to_limbs();for t in a{assert!(t<2147483647);}for t in b{assert!(t<2147483647);}
 let z=NCG_e(); // canonical carrier only; no product relation
 unsafe {let i=NCG_WCALLS;assert!(i<4);NCG_WX[i]=a;NCG_WY[i]=b;NCG_WO[i]=z.to_limbs();NCG_WCALLS+=1;}z
}
fn NCG_horner(alpha:E,h:E,p:E)->E{h.add(alpha.mul(p))}
fn NCG_horner_log_case(three:bool,negative:bool){
 let a=NCG_e();let h=[NCG_e(),NCG_e(),NCG_e(),NCG_e()];let k:usize=kani::any();kani::assume(k<8);
 let mut out=NCG_horner(a,h[2],h[3]);
 if three{out=NCG_horner(a,h[1],out);out=NCG_horner(a,h[0],out);}
 unsafe{
 assert_eq!(NCG_WCALLS,if three{3}else{1});assert_eq!(NCG_WX[0][k],a.to_limbs()[k]);assert_eq!(NCG_WY[0][k],h[3].to_limbs()[k]);
 let z0=E::from_limbs(NCG_WO[0]).unwrap();let t0=h[2].add(z0);
 let expected=if three{
  assert_eq!(NCG_WX[1][k],a.to_limbs()[k]);assert_eq!(NCG_WY[1][k],t0.to_limbs()[k]);
  let t1=h[1].add(E::from_limbs(NCG_WO[1]).unwrap());assert_eq!(NCG_WX[2][k],a.to_limbs()[k]);assert_eq!(NCG_WY[2][k],t1.to_limbs()[k]);
  h[0].add(E::from_limbs(NCG_WO[2]).unwrap())
 }else{t0};
 if negative{assert_ne!(out.to_limbs()[k],expected.to_limbs()[k]);}else{assert_eq!(out.to_limbs()[k],expected.to_limbs()[k]);}
 }
}
'''
for typ,body,stub in [
 ('single','NCG_postread_case(false,NEG)','#[kani::stub(NCG_add_expression,NCG_add_spec)]\n'),
 ('eight','NCG_postread_case(true,NEG)','#[kani::stub(NCG_add_expression,NCG_add_spec)]\n'),
 ('horner_one','NCG_horner_log_case(false,NEG)','#[kani::stub(aspis_core::field::WideExact::mul,NCG_wide_opaque)]\n'),
 ('horner_three','NCG_horner_log_case(true,NEG)','#[kani::stub(aspis_core::field::WideExact::mul,NCG_wide_opaque)]\n')]:
 for neg in [False,True]:s+=attrs+stub+'fn NCG_'+typ+('_negative' if neg else '')+'(){'+body.replace('NEG',str(neg).lower())+';}\n'
Path('/tmp/NCG_native.rs').write_text(s)
(E/'NCG_native.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
