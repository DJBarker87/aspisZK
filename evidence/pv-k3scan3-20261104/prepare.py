from pathlib import Path
import subprocess,json,hashlib,lzma,base64,shutil
E=Path(__file__).resolve().parent;OLD=E.parent/'pv-k3scan-20261101'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(r,p):return subprocess.check_output(['git','show',r+':'+p])
def body(t,n):
 a=t.index('fn '+n+'(');a=t.rfind('\n',0,a)+1;s=t.index('{',a);d=1;i=s
 while d:i+=1;d+=(t[i]=='{')-(t[i]=='}')
 return t[a:i+1]
pins={'entry':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'branch':subprocess.check_output(['git','branch','--show-current'],text=True).strip(),'research':subprocess.check_output(['git','rev-parse','research'],text=True).strip(),'allowed_ids':'K91900-K91959','Lean':0,'scope':['C051','C053','C156','C163','C164']}
(E/'PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
P=E/'caller';P.mkdir(exist_ok=True)
(P/'Cargo.toml').write_text('''[package]
name="pv-k3-native-callers"
version="0.0.0"
edition="2021"
[workspace]
[lib]
path="lib.rs"
[features]
negative-control=[]
[dependencies]
aspis-core={path="../source/crates/aspis-core"}
[profile.dev]
opt-level=3
overflow-checks=false
''')
# Reuse complete pinned project closure; no second corpus, payload only.
x=json.loads(lzma.decompress((OLD/'B3-source.json.xz').read_bytes()))
files={n:base64.b64decode(b) for n,b in x.items() if n.startswith('crates/aspis-core/') or n.startswith('docs/research/v8-r0-zk-20261009/refine/poseidon/') or n in ['Cargo.toml','Cargo.lock']}
# Workspace root contains only the reached core dependency and its pinned inherited metadata.
t=files['Cargo.toml'].decode();import re
t=re.sub(r'members\s*=\s*\[.*?\]', 'members=["crates/aspis-core","docs/research/v8-r0-zk-20261009/refine/poseidon"]',t,count=1,flags=re.S);files['Cargo.toml']=t.encode()
raw=json.dumps({n:base64.b64encode(b).decode() for n,b in files.items()}).encode();(E/'source.json.xz').write_bytes(lzma.compress(raw));(E/'source.json.sha256').write_text(sha(raw)+'\n')
# Retain full frozen caller origins. Selected function bodies are emitted byte-for-byte.
orig={}
for name,path in [('host','host_terminal_kani16.rs'),('reference','reference_terminal_kani16.rs'),('memo','shared_callee16.rs')]:
 t=git('4bc59099b98552f79d92d2a2ce289dab3faedbaa','tools/pv-b3p6-20261028/v244/'+path).decode();orig[name]=t;(E/(name+'.frozen.rs')).write_text(t)
header='use aspis_core::field::{QM31,CM31,M31};\n#[derive(Clone,Copy)] struct Selectors {high:[QM31;64],low:[QM31;16]}\n'
for name in ['host','reference']:
 (P/(name+'.rs')).write_text(header+body(orig[name],'sum_high')+'\n'+body(orig[name],'sum')+'\n')
# Original function names and original complete return carriers retained.
(P/'lib.rs').write_text('''use aspis_core::field::{QM31,CM31,M31};
mod host; mod reference;
fn q()->QM31 {let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn qs<const N:usize>()->[QM31;N] {let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a}
fn check(a:QM31,b:QM31) {if cfg!(feature="negative-control") {assert_ne!(a,b);}else{assert_eq!(a,b);}}
mod equivalence17 {
 use super::*;
 #[kani::proof] #[kani::unwind(256)]
 fn sum_high_nodes() {let h=qs();let l=qs();let ranges=[4..25,33..57];let mut log=();let a=caller(h,l,&ranges,&mut log);check(a,reference::sum(h,l,&ranges));}
 #[kani::proof] #[kani::unwind(256)]
 fn sum_high_path() {let h=qs();let l=qs();let ranges=[57..63];let mut log=();let a=caller(h,l,&ranges,&mut log);check(a,reference::sum(h,l,&ranges));}
 // No mul/square child is reached by this frozen cone. Empty modifies/effect set.
 fn caller(h:[QM31;64],l:[QM31;16],r:&[core::ops::Range<usize>],_log:&mut ())->QM31 {host::sum(h,l,r)}
}
''')
# Empty Vec native caller is exact; a reached destructor fails, proving its child domain empty.
a=git('87da969edd579ea6740403f808cdfa6ebfc3f5bf','tools/pv-dlib-20261028/array-native.rs').decode();(E/'array.frozen.rs').write_text(a)
a=a.replace('static mut DROPS:usize=0;','').replace('unsafe{DROPS+=1;}','panic!("unexpected Token::drop: empty child domain");').replace('assert_eq!(unsafe{DROPS},0);','let mut log=();\n        frame_empty(&mut log);\n        if cfg!(feature="negative-control") { assert!(false,"corrupt empty Drop log"); }')
a+='\nfn frame_empty(_log:&mut ()) {}\n';a=a.replace('frame_empty(&mut log)','super::frame_empty(&mut log)')
(P/'array.rs').write_text(a)
with (P/'lib.rs').open('a') as f:f.write('\n#[path="array.rs"] mod array;\n')
(E/'SOURCE-ERASURE.json').write_text(json.dumps({'host_sum_high_exact':body(orig['host'],'sum_high') in (P/'host.rs').read_text(),'reference_sum_high_exact':body(orig['reference'],'sum_high') in (P/'reference.rs').read_text(),'sum_high_child_cone':'add/index/iteration only; original mul/square stubs unreachable; complete raw QM31 inputs retained','C051':'Token remains a non-Copy Drop ZST; destructor fail-fast proves zero calls, never a populated-vector property','remaining':'C053 and C156 native oracle adaptation pending'},indent=2)+'\n')
print('prepared frozen cones')
