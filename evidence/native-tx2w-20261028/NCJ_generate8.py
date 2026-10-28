from NCJ_host import *
import difflib
admit('NCJ_INSTALL010')
r=py(f"from pathlib import Path;print((Path({B!r})/'NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs').read_text(),end='')");assert r.returncode==0
before=r.stdout
extra=r'''
static mut NCJ_CN:usize=0;static mut NCJ_CI:[usize;5]=[0;5];static mut NCJ_CO:[E;5]=[E::ZERO;5];static mut NCJ_FAIL:usize=0;
static mut NCJ_A:[E;2]=[E::ZERO;2];static mut NCJ_AP0:[E;4]=[E::ZERO;4];static mut NCJ_AP1:[E;4]=[E::ZERO;4];static mut NCJ_BYTE:u8=0;static mut NCJ_OFFSET:usize=0;
fn NCJ_kind(w:&Weights,kind:usize,alpha:&[E],f:&[u8],folds:usize,n:usize,ap0:&[E;4],ap1:&[E;4],scratch:&mut Vec<K>,parts:&mut[E;7])->Result<(),Error>{
 assert_eq!(w.variant,Variant::S2);assert_eq!(folds,2);assert_eq!(n,64);assert_eq!(scratch.len(),64);assert_eq!(alpha.len(),2);assert_eq!(f.len(),2048);
 let value=ce();unsafe{assert_eq!(alpha[0],NCJ_A[0]);assert_eq!(alpha[1],NCJ_A[1]);assert_eq!(*ap0,NCJ_AP0);assert_eq!(*ap1,NCJ_AP1);assert_eq!(f[NCJ_OFFSET],NCJ_BYTE);
 let i=NCJ_CN;assert!(i<5);NCJ_CI[i]=kind;NCJ_CO[i]=value;NCJ_CN=i+1;if i==NCJ_FAIL{return Err(Error::Parse);}}
 parts[kind]=value;Ok(())
}
fn regular_gate(shared:bool,bad:bool){
 let w=Weights{variant:Variant::S2,factors:[[[K::ZERO;4];5];5],points:[[K::ZERO;10];3],extra:[K::ZERO;2]};let alpha=[ce(),ce()];let ap0=[ce(),ce(),ce(),ce()];let ap1=[ce(),ce(),ce(),ce()];let mut parts=[ce(),ce(),ce(),ce(),ce(),ce(),ce()];let old=parts;let mut scratch=KMX_scratch();
 let mut f=[0u8;2048];let offset:usize=kani::any();kani::assume(offset<2048);let byte:u8=kani::any();kani::assume(offset%4!=3||byte<128);f[offset]=byte;let limit=if shared{3}else{5};let fail:usize=kani::any();kani::assume(fail<=limit);
 unsafe{NCJ_CN=0;NCJ_FAIL=fail;NCJ_A=alpha;NCJ_AP0=ap0;NCJ_AP1=ap1;NCJ_BYTE=byte;NCJ_OFFSET=offset;}
 let result=process_regular_kinds(&w,shared,&alpha,&f,2,64,&ap0,&ap1,&mut scratch,&mut parts);
 let order=if shared{[2usize,5,6,0,0]}else{[1,2,3,5,6]};let calls=if fail<limit{fail+1}else{limit};
 unsafe{assert_eq!(NCJ_CN,calls);for i in 0..calls{assert_eq!(NCJ_CI[i],order[i]+if bad{1}else{0});}
 assert_eq!(result,if fail<limit{Err(Error::Parse)}else{Ok(())});let kind:usize=kani::any();kani::assume(kind<7);let mut expected=old[kind];for i in 0..core::cmp::min(fail,limit){if order[i]==kind{expected=NCJ_CO[i];}}assert_eq!(parts[kind],expected);}
}
fn KMX_scratch()->Vec<K>{[K::ZERO;64].to_vec()}
fn reject_gate(bad:bool){let w=Weights{variant:Variant::S2,factors:[[[K::ZERO;4];5];5],points:[[K::ZERO;10];3],extra:[K::ZERO;2]};let alpha=[ce(),ce()];let bytes=[0u8;32];let result=w.pair(&alpha,&bytes,ce());if bad{assert!(result.is_ok());}else{assert_eq!(result,Err(Error::Parse));}}
'''
attrs='''#[kani::proof] #[kani::unwind(66)]
#[kani::stub(super::process_kind,NCJ_kind)]
#[kani::stub(K::mul,NCJ_qmul)]
#[kani::stub(E::mul,NCJ_emul)]
#[kani::stub(E::mul_qm31,NCJ_eqmul)]
#[kani::stub(E::mul_m31,NCJ_emmul)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[K]>::to_vec,crate::KMX_stubs::KMX_to_vec)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
'''
for shared in [False,True]:
 for bad in [False,True]:extra+=attrs+f'fn NCJ_regular_{int(shared)}_{"negative" if bad else "positive"}(){{regular_gate({str(shared).lower()},{str(bad).lower()});}}\n'
for bad in [False,True]:extra+=attrs+f'fn NCJ_reject_{"negative" if bad else "positive"}(){{reject_gate({str(bad).lower()});}}\n'
after=before+extra
(E/'NCJ_stage8.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/NCJ_weights.rs',tofile='b/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')))
r=py(f'''from pathlib import Path
p=Path({(B+'/NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')!r});assert p.read_text()=={before!r};p.write_text({after!r})
''');assert r.returncode==0,r.stderr
