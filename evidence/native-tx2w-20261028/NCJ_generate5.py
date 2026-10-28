from NCJ_host import *
import difflib
admit('NCJ_INSTALL007')
r=py(f"from pathlib import Path;print((Path({B!r})/'NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs').read_text(),end='')");assert r.returncode==0
before=r.stdout
extra=r'''
fn factor_address_gate(bad:bool){
 let k:usize=kani::any();let d:usize=kani::any();kani::assume(k<5&&d<5);let f=[cq(),cq(),cq(),cq()];let x=cq();
 let mut w=weights();w.factors[k][d]=f;reset();
 let out=[x.mul(w.factors[k][d][0]),x.mul(w.factors[k][d][1]),x.mul(w.factors[k][d][2]),x.mul(w.factors[k][d][3])];
 let i:usize=kani::any();kani::assume(i<4);unsafe{assert_eq!(NCJ_QN,4);assert_eq!(NCJ_QL[i].0,x);assert_eq!(NCJ_QL[i].1,if bad{f[i].add(K::ONE)}else{f[i]});assert_eq!(out[i],NCJ_QL[i].2);}
}
fn kind_index_gate(bad:bool){
 let kind:usize=kani::any();kani::assume(kind==1||kind==2||kind==3||kind==5||kind==6);
 let k=if kind<4{kind-1}else{kind-2};
 assert!(k<5);let expected=match kind{1=>0,2=>1,3=>2,5=>3,_=>4};assert_eq!(k,expected+if bad{1}else{0});
}
fn box_window_gate(mode:u8,bad:bool){
 let mut factors=[[[K::ZERO;4];5];5];let mut points=[[K::ZERO;10];3];let mut extra=[K::ZERO;2];let value=cq();
 let k:usize=kani::any();let d:usize=kani::any();let lane:usize=kani::any();kani::assume(k<5&&d<5&&lane<4);
 let p:usize=kani::any();let c:usize=kani::any();let e:usize=kani::any();kani::assume(p<3&&c<10&&e<2);
 if mode==0{factors[k][d][lane]=value;}if mode==1{points[p][c]=value;}if mode==2{extra[e]=value;}
 let out=Weights::box_from_parts(Variant::S2,factors,points,extra);
 assert_eq!(out.variant,Variant::S2);let after=match mode{0=>out.factors[k][d][lane],1=>out.points[p][c],_=>out.extra[e]};assert_eq!(after,if bad{value.add(K::ONE)}else{value});
}
'''
attrs='''#[kani::proof] #[kani::unwind(66)]
#[kani::stub(K::mul,NCJ_qmul)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
'''
for name in ['factor_address','kind_index']:
 for bad in [False,True]:extra+=attrs+f'fn NCJ_{name}_{"negative" if bad else "positive"}(){{{name}_gate({str(bad).lower()});}}\n'
for mode in range(3):
 for bad in [False,True]:extra+=attrs+f'fn NCJ_box_{mode}_{"negative" if bad else "positive"}(){{box_window_gate({mode},{str(bad).lower()});}}\n'
after=before+extra
(E/'NCJ_stage5.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/NCJ_weights.rs',tofile='b/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')))
r=py(f'''from pathlib import Path
p=Path({(B+'/NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')!r});assert p.read_text()=={before!r};p.write_text({after!r})
''');assert r.returncode==0,r.stderr
