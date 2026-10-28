from NCJ_host import *
import difflib
admit('NCJ_INSTALL006')
source=r'''
use super::*;
use aspis_core::r0::CodeField;
fn word()->u32{let x:u32=kani::any();kani::assume(x<2147483647);x}
fn ce()->E{E::from_limbs([word(),word(),word(),word(),word(),word(),word(),word()]).unwrap()}
static mut NCJ_SEEK:usize=0;
static mut NCJ_FN:usize=0;static mut NCJ_FV:[E;2]=[E::ZERO;2];static mut NCJ_FI:[usize;2]=[0;2];static mut NCJ_FB:[u8;2]=[0;2];static mut NCJ_FL:[usize;2]=[0;2];
static mut NCJ_MN:usize=0;static mut NCJ_MX:E=E::ZERO;static mut NCJ_MY:M31=M31::ZERO;static mut NCJ_MO:E=E::ZERO;
static mut NCJ_PN:usize=0;static mut NCJ_PX:E=E::ZERO;static mut NCJ_PB:u8=0;static mut NCJ_PL:usize=0;static mut NCJ_PO:E=E::ZERO;
fn NCJ_field(b:&[u8],j:usize)->E{let v=ce();unsafe{let k=NCJ_FN;assert!(k<2);assert!(j<7);assert_eq!(b.len(),224);NCJ_FV[k]=v;NCJ_FI[k]=j;NCJ_FB[k]=b[NCJ_SEEK];NCJ_FL[k]=b.len();NCJ_FN=k+1;}v}
fn NCJ_scale(x:E,y:M31)->E{let v=ce();unsafe{NCJ_MN+=1;NCJ_MX=x;NCJ_MY=y;NCJ_MO=v;}v}
fn NCJ_poly(b:&[u8],x:E)->E{let v=ce();unsafe{NCJ_PN+=1;NCJ_PX=x;NCJ_PB=b[NCJ_SEEK];NCJ_PL=b.len();NCJ_PO=v;}v}
fn canonical_poly()->[u8;224]{
 let b:[u8;224]=kani::any();for i in 0..56{let a=u32::from_le_bytes([b[4*i],b[4*i+1],b[4*i+2],b[4*i+3]]);kani::assume(a<2147483647);}b
}
fn round_gate(bad:bool){
 let bytes=canonical_poly();let alpha=ce();let claim=ce();let round:usize=kani::any();kani::assume(round<2);let seek:usize=kani::any();kani::assume(seek<224);
 unsafe{NCJ_SEEK=seek;NCJ_FN=0;NCJ_MN=0;NCJ_PN=0;}
 let out=finish_relation_round(&bytes,alpha,claim,round);
 unsafe{
 assert_eq!(NCJ_FN,2);assert_eq!(NCJ_FI[0],0);assert_eq!(NCJ_FI[1],4);assert_eq!(NCJ_FB[0],bytes[seek]);assert_eq!(NCJ_FB[1],bytes[seek]);assert_eq!(NCJ_FL[0],224);assert_eq!(NCJ_FL[1],224);
 assert_eq!(NCJ_MN,1);assert_eq!(NCJ_MX,claim);assert_eq!(NCJ_MY,QUARTER);
 let lhs=NCJ_FV[0].add(NCJ_FV[1]);
 if lhs!=NCJ_MO{assert_eq!(out,Err(Error::Relation));assert_eq!(NCJ_PN,0);}else{
 assert_eq!(NCJ_PN,1);assert_eq!(NCJ_PX,alpha);assert_eq!(NCJ_PL,224);assert_eq!(NCJ_PB,bytes[seek]);assert_eq!(out,Ok(if bad{NCJ_PO.add(E::ONE)}else{NCJ_PO}));}
 }
}
// One literal Horner closure update on an arbitrary prestate. Decoder and
// multiplication are logged at their actual argument carriers.
fn horner_gate(bad:bool){
 let bytes=canonical_poly();let x=ce();let a=ce();let i:usize=kani::any();kani::assume(i<7);let seek:usize=kani::any();kani::assume(seek<224);
 unsafe{NCJ_SEEK=seek;NCJ_FN=0;NCJ_MN=0;}
 let out=a.mul(x).add(field(&bytes,i));
 unsafe{assert_eq!(NCJ_MN,1);assert_eq!(NCJ_MX,a);assert_eq!(NCJ_PX,x);assert_eq!(NCJ_FN,1);assert_eq!(NCJ_FI[0],i);assert_eq!(NCJ_FB[0],bytes[seek]);let expected=NCJ_MO.add(NCJ_FV[0]);assert_eq!(out,if bad{expected.add(E::ONE)}else{expected});}
}
fn NCJ_mul(x:E,y:E)->E{let out=ce();unsafe{NCJ_MN+=1;NCJ_MX=x;NCJ_PX=y;NCJ_MO=out;}out}
'''
attrs='''#[kani::proof] #[kani::unwind(58)]
#[kani::stub(crate::weights::field,NCJ_field)]
#[kani::stub(E::mul_m31,NCJ_scale)]
#[kani::stub(E::mul,NCJ_mul)]
#[kani::stub(super::polynomial,NCJ_poly)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
'''
for name in ['round','horner']:
 for bad in [False,True]:source+=attrs+f'fn NCJ_{name}_{"negative" if bad else "positive"}(){{{name}_gate({str(bad).lower()});}}\n'
r=py(f"from pathlib import Path;print((Path({B!r})/'NCJ_src/crates/aspis-r1-cost-probe/src/verifier.rs').read_text(),end='')");assert r.returncode==0
before=r.stdout;after=before+'\n#[cfg(kani)] #[path="NCJ_relation.rs"] mod NCJ_relation;\n'
p='crates/aspis-r1-cost-probe/src/verifier.rs';q='crates/aspis-r1-cost-probe/src/NCJ_relation.rs'
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/'+q));(E/'NCJ_stage4.patch').write_text(patch)
r=py(f'''from pathlib import Path
s=Path({(B+'/NCJ_src')!r});p=s/{p!r};assert p.read_text()=={before!r};p.write_text({after!r});(s/{q!r}).write_text({source!r})
''');assert r.returncode==0,r.stderr
