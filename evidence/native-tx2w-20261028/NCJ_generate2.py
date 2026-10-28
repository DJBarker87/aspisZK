from NCJ_host import *
import difflib
admit('NCJ_INSTALL002')
r=py(f"from pathlib import Path;print((Path({B!r})/'NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs').read_text(),end='')");assert r.returncode==0
before=r.stdout
extra=r'''
const NCJ_P:u32=2147483647;
fn word()->u32 {let a:u32=kani::any();kani::assume(a<NCJ_P);a}
fn cq()->K {K{c0:CM31{a:M31(word()),b:M31(word())},c1:CM31{a:M31(word()),b:M31(word())}}}
fn ce()->E {E::from_limbs([word(),word(),word(),word(),word(),word(),word(),word()]).unwrap()}
static mut NCJ_QL:[(K,K,K);32]=[(K::ZERO,K::ZERO,K::ZERO);32];
static mut NCJ_QN:usize=0;
static mut NCJ_EL:[(E,E,E,u8);32]=[(E::ZERO,E::ZERO,E::ZERO,0);32];
static mut NCJ_EN:usize=0;
fn NCJ_qmul(x:K,y:K)->K {let z=cq();unsafe{let i=NCJ_QN;assert!(i<32);NCJ_QL[i]=(x,y,z);NCJ_QN=i+1;}z}
fn NCJ_emul(x:E,y:E)->E {let z=ce();unsafe{let i=NCJ_EN;assert!(i<32);NCJ_EL[i]=(x,y,z,0);NCJ_EN=i+1;}z}
fn NCJ_eqmul(x:E,y:K)->E {let z=ce();unsafe{let i=NCJ_EN;assert!(i<32);NCJ_EL[i]=(x,E::from_qm31(y),z,1);NCJ_EN=i+1;}z}
fn NCJ_emmul(x:E,y:M31)->E {let z=ce();unsafe{let i=NCJ_EN;assert!(i<32);NCJ_EL[i]=(x,E::from_m31(y),z,2);NCJ_EN=i+1;}z}
fn reset(){unsafe{NCJ_QN=0;NCJ_EN=0;}}
// Fission at weights.rs:24. Full frozen body, including BOTH multiplications.
fn double_gate(bad:bool){
 let x=cq();reset();let out=double(x);
 unsafe{assert_eq!(NCJ_QN,2);assert_eq!(NCJ_QL[0].0,x);assert_eq!(NCJ_QL[0].1,x);assert_eq!(NCJ_QL[1].0,x);assert_eq!(NCJ_QL[1].1,x);
 let expected=NCJ_QL[0].2.add(NCJ_QL[1].2).sub(K::ONE);assert_eq!(out,if bad{expected.add(K::ONE)}else{expected});}
}
// Exact weights.rs:244..248 inner body, arbitrary prestate and one j.
fn tensor_gate(bad:bool){
 let mut out=[K::ZERO;64];for i in 0..64{out[i]=cq();}
 let old=out;let n=match kani::any::<u8>()%3 {0=>1usize,1=>4,_=>16};
 let j:usize=kani::any();kani::assume(j<n);let f=[cq(),cq(),cq(),cq()];reset();
 let x=out[j];
 out[j+0*n]=x.mul(f[0]);out[j+1*n]=x.mul(f[1]);out[j+2*n]=x.mul(f[2]);out[j+3*n]=x.mul(f[3]);
 unsafe{assert_eq!(NCJ_QN,4);for lane in 0..4 {assert_eq!(NCJ_QL[lane].0,old[j]);assert_eq!(NCJ_QL[lane].1,f[lane]);assert_eq!(out[j+lane*n],NCJ_QL[if bad{(lane+1)%4}else{lane}].2);}}
 let i:usize=kani::any();kani::assume(i<64);if i%n!=j || i>=4*n {assert_eq!(out[i],old[i]);}
}
// Exact scalar_factor fold closure, one arbitrary s, after index/read boundaries.
fn scalar_gate(bad:bool){
 let f=[cq(),cq(),cq(),cq()];let p=[ce(),ce(),ce(),ce()];let v=ce();
 let s:usize=kani::any();kani::assume(s<4);reset();
 let out=v.add(p[PERM[s]].mul_qm31(f[s]));
 unsafe{assert_eq!(NCJ_EN,1);assert_eq!(NCJ_EL[0].0,p[PERM[s]]);assert_eq!(NCJ_EL[0].1,E::from_qm31(f[s]));assert_eq!(NCJ_EL[0].3,1);let expected=v.add(NCJ_EL[0].2);assert_eq!(out,if bad{expected.add(E::ONE)}else{expected});}
}
// Exact Weights::new statement factor cell, one k,d after points reads.
fn factors_gate(bad:bool){
 let a=cq();let b=cq();reset();
 let out=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
 unsafe{assert_eq!(NCJ_QN,4);assert_eq!(NCJ_QL[0].0,K::ONE.sub(a));assert_eq!(NCJ_QL[0].1,K::ONE.sub(b));assert_eq!(NCJ_QL[1].0,a);assert_eq!(NCJ_QL[1].1,K::ONE.sub(b));assert_eq!(NCJ_QL[2].0,K::ONE.sub(a));assert_eq!(NCJ_QL[2].1,b);assert_eq!(NCJ_QL[3].0,a);assert_eq!(NCJ_QL[3].1,b);for i in 0..4{assert_eq!(out[i],NCJ_QL[if bad{(i+1)%4}else{i}].2);}}
}
// Exact Pair common[16] source update, one j.
fn common_gate(bad:bool){
 let f2=[cq(),cq(),cq(),cq()];let f3=[cq(),cq(),cq(),cq()];
 let mut common=[K::ZERO;16];for i in 0..16{common[i]=cq();}
 let old=common;let j:usize=kani::any();kani::assume(j<16);reset();
 common[j]=f2[j&3].mul(f3[j>>2u32]);
 unsafe{assert_eq!(NCJ_QN,1);assert_eq!(NCJ_QL[0].0,f2[j%4]);assert_eq!(NCJ_QL[0].1,f3[j/4]);assert_eq!(common[j],if bad{NCJ_QL[0].2.add(K::ONE)}else{NCJ_QL[0].2});}
 let i:usize=kani::any();kani::assume(i<16 && i!=j);assert_eq!(common[i],old[i]);
}
// Exact Pair low[16] source update, one s.
fn low_gate(bad:bool){
 let ap0=[ce(),ce(),ce(),ce()];let ap1=[ce(),ce(),ce(),ce()];let mut low=[E::ZERO;16];for i in 0..16{low[i]=ce();}
 let old=low;let s:usize=kani::any();kani::assume(s<16);reset();
 low[s]=ap0[PERM[s%4]].mul(ap1[PERM[s/4]]).mul_m31(QUARTER.mul(QUARTER));
 unsafe{assert_eq!(NCJ_EN,2);assert_eq!(NCJ_EL[0].0,ap0[PERM[s%4]]);assert_eq!(NCJ_EL[0].1,ap1[PERM[s/4]]);assert_eq!(NCJ_EL[0].3,0);assert_eq!(NCJ_EL[1].0,NCJ_EL[0].2);assert_eq!(NCJ_EL[1].1,E::from_m31(M31(134217728)));assert_eq!(NCJ_EL[1].3,2);assert_eq!(low[s],if bad{NCJ_EL[1].2.add(E::ONE)}else{NCJ_EL[1].2});}
 let i:usize=kani::any();kani::assume(i<16 && i!=s);assert_eq!(low[i],old[i]);
}
'''
# QUARTER.mul(QUARTER) is multiplication too: supply a separate exact constant
# returned by an opaque base stub; no native field product is ever unwound.
extra=extra.replace('static mut NCJ_QL:', 'fn NCJ_quarter_mul(x:M31,y:M31)->M31 {assert_eq!(x,QUARTER);assert_eq!(y,QUARTER);M31(134217728)}\nstatic mut NCJ_QL:')
attrs='''#[kani::proof] #[kani::unwind(66)]
#[kani::stub(K::mul,NCJ_qmul)]
#[kani::stub(E::mul,NCJ_emul)]
#[kani::stub(E::mul_qm31,NCJ_eqmul)]
#[kani::stub(E::mul_m31,NCJ_emmul)]
#[kani::stub(M31::mul,NCJ_quarter_mul)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
'''
for name in ['double','tensor','scalar','factors','common','low']:
 for bad in [False,True]:extra+=attrs+f'fn NCJ_{name}_{"negative" if bad else "positive"}(){{{name}_gate({str(bad).lower()});}}\n'
after=before+extra
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/NCJ_weights.rs',tofile='b/crates/aspis-r1-cost-probe/src/NCJ_weights.rs'))
(E/'NCJ_stage2.patch').write_text(patch)
r=py(f'''from pathlib import Path
p=Path({(B+'/NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')!r});assert p.read_text()=={before!r};p.write_text({after!r})
''');assert r.returncode==0,r.stderr
