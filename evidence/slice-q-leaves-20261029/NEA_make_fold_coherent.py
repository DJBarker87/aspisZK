from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NEA_payload import save
p=json.loads((E/'NEA_PAYLOAD.json').read_text());k='crates/aspis-r1-cost-probe/src/NEA_fold.rs';s=p[k]
a=s.index('#[derive(Clone,Copy)] pub(super) struct EMEntry');b=s.index('pub(super) unsafe fn reset')
n=''
for name,fn,T,U,V,N in [('EM','em','E','E','E',3),('SM','sm','E','M31','E',6),('BM','bm','M31','M31','M31',4)]:
 zT='E::ZERO' if T=='E' else 'M31::ZERO';zU='E::ZERO' if U=='E' else 'M31::ZERO';zV='E::ZERO' if V=='E' else 'M31::ZERO'
 pred=('canon(x)' if T=='E' else 'true')+'&&'+('canon(y)' if U=='E' else 'true' if name=='BM' else 'y.0<P')
 # SM scalar must be canonical; BM accepts every raw u32.
 if name=='SM':pred='canon(x)&&y.0<P'
 n+=f'''#[derive(Clone,Copy)] pub(super) struct {name}Entry{{x:{T},y:{U},out:{V}}}
pub(super) struct {name}Memo{{count:usize,slots:[{name}Entry;{N}]}}
pub(super) static mut {name}:{name}Memo={name}Memo{{count:0,slots:[{name}Entry{{x:{zT},y:{zU},out:{zV}}};{N}]}};
fn {fn}(x:{T},y:{U})->{V}{{assert!({pred});unsafe{{
'''
 n+='let out=any_e();\n' if V=='E' else 'let w:u32=kani::any();kani::assume(w<P);let out=M31(w);\n'
 for j in range(N):n+=f'if {name}.count>{j}{{kani::assume(x!={name}.slots[{j}].x||y!={name}.slots[{j}].y||out=={name}.slots[{j}].out);}}\n'
 n+=f'assert!({name}.count<{N});let k={name}.count;{name}.slots[k]={name}Entry{{x,y,out}};{name}.count+=1;out}}}}\n'
 n+=f'fn {fn}_replay(x:{T},y:{U})->{V}{{assert!({pred});unsafe{{\n'
 for j in range(N):n+=f'if {name}.count>{j}&&{name}.slots[{j}].x==x&&{name}.slots[{j}].y==y{{return {name}.slots[{j}].out;}}\n'
 n+='panic!("reference operand has no matching native call");}}\n'
s=s[:a]+n+s[b:];p[k]=s;save(p);(E/'NEA_fold_coherent.rs.txt').write_text(s)
