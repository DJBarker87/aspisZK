from pathlib import Path
import json,hashlib
out=Path('evidence/pv-d188-20261027');d=out/'tests/native2-files';bindings=[]
def item(p,n):
 t=Path(p).read_text();a=t.index(n);b=t.index('{',a);depth=1;i=b+1
 while depth:
  if t[i]=='{':depth+=1
  elif t[i]=='}':depth-=1
  i+=1
 s=t[a:i];bindings.append(dict(path=p,line=t.count('\n',0,a)+1,sha256=hashlib.sha256(s.encode()).hexdigest()));return s
s='mod field;use field::{M31,QM31};const STATE_ONLY_POSEIDON_TRACE_ROWS:usize=1024;const MAX_BATCH:usize=16;const LEAF_BITS:u32=18;\n'
s+='#[derive(Debug)]'+item('crates/aspis-prover/src/state_only_hiding.rs','pub enum StateOnlyMaskBuildError')+'\n'
for n in ['fn check_indices(','fn count_parent(','fn count_level(','fn count_levels(','fn node_count(']:s+=item('crates/aspis-r1-cost-probe/src/host_tree.rs',n)+'\n'
s+=item('crates/aspis-r1-cost-probe/src/host_semantic.rs','fn boolean_point(')+'\n'
for n in ['fn interpolation_shift(','fn interpolation_basis_cell(','fn interpolation_extend(','fn interpolation_basis_steps(','fn interpolation_basis(','fn interpolation_accumulate(']:s+=item('crates/aspis-r1-cost-probe/src/host_sumcheck.rs',n)+'\n'
for n in ['fn inactive_m31_step(','fn inactive_qm31_step(','fn sum_m31_copy_inactive(','fn sum_qm31_copy_inactive(','fn balance_m31_copy_inactive(','fn balance_qm31_copy_inactive(']:s+=item('crates/aspis-prover/src/state_only_hiding.rs',n)+'\n'
t=Path('crates/aspis-r1-cost-probe/src/host_sumcheck.rs').read_text();a=t.index('let mut offset=0;',t.index('fn evaluate_assignment'));b=t.index('oracle.evaluate(&at)',a);fragment=t[a:b]
s+='fn assignment_fill(round:usize,remaining:usize,assignment:usize,mut at:[QM31;10])->[QM31;10]{'+fragment+'at}\n'
s+='''fn main(){println!("nodes {:?}",node_count(&[1,2,3]));println!("boolean {:?}",boolean_point(37).map(|q|q.c0.a.0));println!("accumulate {:?}",interpolation_accumulate([QM31::ONE;28],&[M31(2);28],QM31::ONE.mul_m31(M31(3))).map(|q|q.c0.a.0));println!("basis_cell {:?}",interpolation_basis_cell([M31(2);28],1,3).map(|q|q.0));println!("extend {:?}",interpolation_extend([M31(2);28],1,3).map(|q|q.0));let(a,d)=interpolation_basis(1);println!("basis {:?} {}",a.map(|q|q.0),d.0);println!("assignment {:?}",assignment_fill(1,3,5,[QM31::ZERO;10]).map(|q|q.c0.a.0));let mut a=[M31::ONE;1024];balance_m31_copy_inactive(&mut a,3,&[false;1024]).unwrap();println!("balance_m31 {}",a[3].0);let mut a=[QM31::ONE;1024];balance_qm31_copy_inactive(&mut a,3,&[false;1024]).unwrap();println!("balance_qm31 {}",a[3].c0.a.0);}\n'''
(d/'native7.rs').write_text(s);(out/'native8-source-binding.json').write_text(json.dumps(dict(fragments=bindings,assignment_loop_fragment_sha256=hashlib.sha256(fragment.encode()).hexdigest(),assignment_note='Exact loop from host_sumcheck.rs:134–137, captured before the opaque oracle call; not a whole oracle/native-Result refinement.'),indent=2)+'\n')
p=Path('tools/pv-d188-20261027/native.py');t=p.read_text().replace("'native-007':'native2-files/native6.rs'","'native-007':'native2-files/native6.rs','native-008':'native2-files/native7.rs'");p.write_text(t)
