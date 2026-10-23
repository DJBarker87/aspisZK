from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'stored-binding.rs' not in s:s+='\ninclude!("stored-binding.rs");\n'
p.write_text(s)
(E/'native/stored-binding.rs').write_text('''
fn native_raw_s2(factors:[[[E;4];5];5],extra:[E;2],kind:usize,j:usize,inactive:bool)->E {
 match kind {
  0=>if inactive {E::ONE}else{E(0)},
  4=>if j<56 {power_call(extra[j/28],(j%28) as u64)}else{E(0)},
  _=>{let k=if kind<4 {kind-1}else{kind-2};
   (0..5).fold(E::ONE,|v,d|v.mul(factors[k][d][(j>>(2*d))&3]))}
 }
}
fn owner_stored_step(rows:[[E;4];5],j:usize,d:usize,acc:E)->E {
 let digit=(j>>((2*d) as u32))&3;acc.mul(rows[d][digit])
}
fn owner_raw_s2(factors:[[[E;4];5];5],extra:[E;2],kind:usize,j:usize,inactive:bool)->E {
 if kind==0 {if inactive {E::ONE}else{E(0)}} else if kind==4 {
  owner_libra(extra,j)
 } else {
  let k=if kind<4 {kind-1}else{kind-2};let mut acc=E::ONE;
  for d in 0..5 {acc=owner_stored_step(factors[k],j,d,acc);}acc
 }
}
#[cfg(kani)] mod stored_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(128)] fn full_raw_dispatch() {
  let factors:[[[E;4];5];5]=unsafe{core::mem::transmute(kani::any::<[u32;100]>())};
  let extra=[E(kani::any()),E(kani::any())];let answers=kani::any();
  let kind:usize=kani::any();let j:usize=kani::any();let inactive:bool=kani::any();kani::assume(kind<7 && j<1024);
  reset(answers);let x=native_raw_s2(factors,extra,kind,j,inactive);let tx=trace();
  reset(answers);let y=owner_raw_s2(factors,extra,kind,j,inactive);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);
 }
}
''')
p=Path('crates/aspis-r1-cost-probe/src/weights.rs')
(E/'pins/stored-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),binding='Complete S2 raw dispatch on all seven kinds and legal coefficient indices, arbitrary full stored factors, extra values and inactive Bool. The Bool callee and power operation are separately proved. Every factor shift/mask and read, all five multiplications, and complete operation trace are checked.'),indent=2)+'\n')
