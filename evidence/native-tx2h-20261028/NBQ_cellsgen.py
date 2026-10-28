from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/fast_dots.rs';frozen=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
with tempfile.TemporaryDirectory() as d:
 for src in ['crates/aspis-r1-cost-probe/src/weights.rs',p]:
  q=Path(d)/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(subprocess.check_output(['git','show','4bb3b3f5:'+src],text=True))
 subprocess.run(['git','apply','-'],input=(E/'NBQ_u07.patch').read_text(),cwd=d,text=True,check=True)
 old=(Path(d)/p).read_text()
tail='''\n#[cfg(kani)]\nmod NBQ_cells {\nuse super::*;\n'''
for j in range(8):
 tail+=f'''// Exact after-product cut at source sums[{j}] += coefficient[{j}]*scalar.
 #[kani::proof] #[kani::unwind(64)]
 fn add{j}() {{
  let mut sums:[u64;8]=kani::any();let before=sums;
  let k:u64=kani::any();kani::assume(k<4);
  kani::assume(sums[{j}]<=k*4611686009837453316);
  let product:u64=kani::any();kani::assume(product<=4611686009837453316);
  sums[{j}]+=product;
  let at:usize=kani::any();kani::assume(at<8);
  assert!(sums[at]==if at=={j}{{before[at]+product}}else{{before[at]}});
  assert!(sums[{j}]<18446744073709551615);
 }}
'''
tail+=r'''
 #[kani::proof] #[kani::unwind(64)]
 fn fold_add(){
  let mut limbs:[u64;8]=kani::any();let sums:[u64;8]=kani::any();let before=limbs;
  let group:u64=kani::any();kani::assume(group<7);
  let j:usize=kani::any();kani::assume(j<8);kani::assume(limbs[j]<=group*10737418238);
  limbs[j]+=(sums[j]&0x7fff_ffff)+(sums[j]>>31);
  let at:usize=kani::any();kani::assume(at<8);
  let folded=(sums[j]%2147483648)+(sums[j]/2147483648);
  assert!(limbs[at]==if at==j{before[at]+folded}else{before[at]});
  assert!(limbs[j]<75161927667);
 }
 #[kani::proof] #[kani::unwind(608)]
 fn selected_scalar(){
  let q:[u8;608]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);let term:usize=kani::any();kani::assume(term<26);
  let at=slot*120+term*4;
  let word=u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]]);
  let scalar=M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap());
  assert!(scalar.is_some()==(word<0x7fff_ffff));if let Some(scalar)=scalar{assert!(scalar.0==word);}
 }
 #[kani::proof] #[kani::unwind(8)]
 fn groups_initial(){let mut iter=(0usize..26).step_by(4);assert!(iter.next()==Some(0));}
 #[kani::proof] #[kani::unwind(8)]
 fn groups_continuing(){let group:usize=kani::any();kani::assume(group>=1&&group<7);let mut iter=(4*(group-1)..26).step_by(4);assert!(iter.next()==Some(4*(group-1)));assert!(iter.next()==Some(4*group));}
 #[kani::proof] #[kani::unwind(8)]
 fn groups_done(){let mut iter=(24usize..26).step_by(4);assert!(iter.next()==Some(24));assert!(iter.next()==None);}
}
'''
(E/'NBQ_cells.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+tail).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
