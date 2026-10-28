from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;oldE=E.parent/'native-tx2h-20261028'
p='crates/aspis-r1-cost-probe/src/fast_dots.rs'
paths=[p,'crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs']
with tempfile.TemporaryDirectory() as d:
 for f in paths:
  q=Path(d)/f;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(subprocess.check_output(['git','show','4bb3b3f5:'+f],text=True))
 for patch in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']:
  subprocess.run(['git','apply','-'],input=(oldE/patch).read_text(),cwd=d,text=True,check=True)
 old=(Path(d)/p).read_text()
t='''\n#[cfg(kani)] mod NBS_joined {\nuse super::*;\n// ONE arbitrary source term after its eight product cuts. No multiplication\n// is executed here: NBS_DotTerm.update pairs all eight exact emitted cells.\n#[kani::proof] #[kani::unwind(64)]\nfn eight_cells(){\n let mut sums:[u64;8]=kani::any();let p:[u64;8]=kani::any();let before=sums;\n let n:u64=kani::any();kani::assume(n<4);\n'''
for j in range(8):t+=f' kani::assume(sums[{j}]<=n*4611686009837453316&&p[{j}]<=4611686009837453316);\n'
for j in range(8):t+=f' sums[{j}]+=p[{j}];\n'
for j in range(8):t+=f' assert!(sums[{j}]==before[{j}]+p[{j}]);assert!(sums[{j}]<18446744073709551615);\n'
t+='''}
// ONE source folded group, all eight words on the SAME pre-state.
#[kani::proof] #[kani::unwind(64)]
fn eight_folds(){
 let sums:[u64;8]=kani::any();let mut limbs:[u64;8]=kani::any();let before=limbs;
 let n:u64=kani::any();kani::assume(n<7);
'''
for j in range(8):t+=f' kani::assume(limbs[{j}]<=n*10737418238);\n'
for j in range(8):t+=f' limbs[{j}]+=(sums[{j}]&0x7fff_ffff)+(sums[{j}]>>31);\n'
for j in range(8):t+=f' assert!(limbs[{j}]==before[{j}]+(sums[{j}]%2147483648)+(sums[{j}]/2147483648));assert!(limbs[{j}]<=75161927666);\n'
t+='}\n}\n'
(E/'NBS_joined.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
