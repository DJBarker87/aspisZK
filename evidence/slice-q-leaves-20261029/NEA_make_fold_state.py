from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NEA_payload import save
old=(E/'NEA_fold_reference.rs.txt').read_text()
s=old.replace('fn add(', 'fn add(&mut self,').replace('fn sub(', 'fn sub(&mut self,').replace('fn mul(', 'fn mul(&mut self,').replace('fn scale(', 'fn scale(&mut self,').replace('fn base_mul(', 'fn base_mul(&mut self,')
s=s.replace('(alpha:E,','(ops:&mut O,alpha:E,').replace('O::','ops.')
# Shared quarter*ix is intentional in the cohort; native repeats it. Replay consumes the duplicate explicitly below.
(E/'NEA_fold_state_reference.rs.txt').write_text(s)
p=json.loads((E/'NEA_PAYLOAD.json').read_text());native=p['crates/aspis-r1-cost-probe/src/NEA_fold.rs']
start=native.index('fn em(');end=native.index('pub(super) unsafe fn reset')
# Replace memo scans by one append per native call. Sequential read-only replay state is local to the postcondition.
new=''
for fn,name,T,U,V,N in [('em','EM','E','E','E',8),('sm','SM','E','M31','E',16),('bm','BM','M31','M31','M31',8)]:
 pred=('canon(x)' if T=='E' else 'x.0<P')+'&&'+('canon(y)' if U=='E' else 'y.0<P')
 out='let out=any_e();' if V=='E' else 'let w:u32=kani::any();kani::assume(w<P);let out=M31(w);'
 new+=f'fn {fn}(x:{T},y:{U})->{V} {{assert!({pred});unsafe{{assert!({name}.count<{N});{out}let k={name}.count;{name}.slots[k]={name}Entry{{x,y,out}};{name}.count+=1;out}}}}\n'
# Preserve declarations interspersed between previous functions.
import re
for decl in re.findall(r'#\[derive\(Clone,Copy\)\] pub\(super\) struct (?:SM|BM)Entry.*?;\n',native[start:end],re.S):
 new=decl+new
# declarations include structs/static through first ; newline (static line ends ;). Verify below through compiler.
native=native[:start]+new+native[end:]
a=native.index('struct Replay;');b=native.index('pub fn circle_post')
rep='struct Replay{ie:usize,is:usize,ib:usize}\nimpl NEA_Ops<E,M31> for Replay {\n fn add(&mut self,x:E,y:E)->E {assert!(canon(x)&&canon(y));x.add(y)}\n fn sub(&mut self,x:E,y:E)->E {assert!(canon(x)&&canon(y));x.sub(y)}\n'
for fn,name,T,U,V,idx in [('mul','EM','E','E','E','ie'),('scale','SM','E','M31','E','is'),('base_mul','BM','M31','M31','M31','ib')]:
 rep+=f'fn {fn}(&mut self,x:{T},y:{U})->{V} {{unsafe{{let k=self.{idx};assert!(k<{name}.count);let e={name}.slots[k];assert!(e.x==x&&e.y==y);self.{idx}+=1;e.out}}}}\n'
rep+='}\n'
native=native[:a]+rep+native[b:]
native=native.replace('let expected=circle_ref::<E,M31,Replay>(alpha,','let expected=circle_ref::<E,M31,Replay>(&mut Replay{ie:0,is:0,ib:0},alpha,').replace('let expected=line_ref::<E,M31,Replay>(alpha,','let expected=line_ref::<E,M31,Replay>(&mut Replay{ie:0,is:0,ib:0},alpha,')
# Frozen circle calls quarter*ix twice; reference mirrors the frozen sequence, after which Lean discharges the shared expression.
s=s.replace('let h3=ops.scale(ops.sub(ops.add(amb,c),d),ops.base_mul(m1,iy));','let m1_again=ops.base_mul(quarter,ix);\n let h3=ops.scale(ops.sub(ops.add(amb,c),d),ops.base_mul(m1_again,iy));')
# Rust nested &mut calls require sequential let expressions; start from exact standalone source below instead.
p['crates/aspis-r1-cost-probe/src/NEA_fold_reference.rs']=s.replace('#![no_std]\n','')
p['crates/aspis-r1-cost-probe/src/NEA_fold.rs']=native
(E/'NEA_fold_state_reference.rs.txt').write_text(s);(E/'NEA_fold_state.rs.txt').write_text(native)
save(p)
