from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());s=x[C+'NGW_new.rs']
a=s.index('fn frame(');b=s.index('fn lookup(',a)
s=s[:a]+r'''fn store(dst:&mut[K;4],row:[K;4]){*dst=row;}
fn frame(g:u8){let mut dst=core::array::from_fn(|_|q(kani::any()));let row=core::array::from_fn(|_|q(kani::any()));store(&mut dst,row);let term:usize=kani::any();kani::assume(term<4);let limb:usize=kani::any();kani::assume(limb<4);let mut expected=words(row[term])[limb];if cfg!(NGW_invert){expected^=1;}assert!(words(dst[term])[limb]==expected);let _=g;}
fn window(g:u8){let mut f=arbitrary();let k:usize=kani::any();kani::assume(k<5);let d:usize=kani::any();kani::assume(d<5);let base=f.as_mut_ptr().cast::<K>();let selected=&mut f[k][d];let mut ptr=selected.as_mut_ptr();let len=selected.len();if cfg!(NGW_invert){ptr=ptr.wrapping_add(1);}assert!(len==4&&ptr==base.wrapping_add((5*k+d)*4));let _=g;}
''' +s[b:]
s+='gate!(write_window,window,0);\n';x[C+'NGW_new.rs']=s
(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGW_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
