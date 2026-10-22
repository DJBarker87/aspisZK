from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent
p=E/'native/lib.rs';s=p.read_text()
if 'round-shape-binding.rs' not in s:s+='\ninclude!("round-shape-binding.rs");\n'
p.write_text(s)
(E/'native/round-shape-binding.rs').write_text('''
const ROUND_PERM49:[usize;4]=[0,3,2,1];
fn native_round256(q:[E;256],w:[E;256],mut out:[E;7],d:usize,s:usize,t:usize)->[E;7] {
 let k=s+ROUND_PERM49[t];out[k]=out[k].add(q[4*d+s].mul(w[4*d+t]));out
}
fn owner_round1024(q:[E;1024],w:[E;1024],mut out:[E;7],d:usize,s:usize,t:usize)->[E;7] {
 let k=s+ROUND_PERM49[t];out[k]=out[k].add(q[4*d+s].mul(w[4*d+t]));out
}
#[cfg(kani)] mod round_shape_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(1030)] fn second_round_shape_iteration() {
  let q:[E;256]=unsafe{core::mem::transmute(kani::any::<[u32;256]>())};
  let w:[E;256]=unsafe{core::mem::transmute(kani::any::<[u32;256]>())};
  let out:[E;7]=unsafe{core::mem::transmute(kani::any::<[u32;7]>())};
  let mut qp=[E(0);1024];let mut wp=[E(0);1024];
  for i in 0..256 {qp[i]=q[i];wp[i]=w[i];}
  let d:usize=kani::any();let s:usize=kani::any();let t:usize=kani::any();kani::assume(d<64 && s<4 && t<4);let answers=kani::any();
  reset(answers);let x=native_round256(q,w,out,d,s,t);let tx=trace();
  reset(answers);let y=owner_round1024(qp,wp,out,d,s,t);let ty=trace();
  assert_eq!(x,y);assert_eq!(tx,ty);assert_eq!(tx.1,2);
 }
}
''')
p=Path('crates/aspis-r1-cost-probe/src/prover.rs')
w=Path('crates/aspis-r1-cost-probe/src/weights.rs')
(E/'pins/round-shape-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),permutation_source=str(w),permutation_sha256=hashlib.sha256(w.read_bytes()).hexdigest(),binding='Native second-round q/w 256-entry input and owned padded 1024 carrier, full seven-output context and complete callee trace, every d<64/s,t<4. The only padded cells are outside all legal reads.'),indent=2)+'\n')
