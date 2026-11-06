from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates','programs'],text=True).splitlines()+['Cargo.toml','Cargo.lock']
d={n:base64.b64encode(subprocess.check_output(['git','show',rev+':'+n])).decode() for n in paths}
raw=json.dumps(d).encode();(E/'NKJ_FROZEN.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NKJ_FROZEN.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
s=(E/'NKJ_run.py').read_text().replace('import subprocess,json,sys,time,shlex,hashlib,lzma','import subprocess,json,sys,time,shlex,hashlib,lzma,base64')
s=s.replace("for name in cfg.pop('upload',[]):files[name]=(E/name).read_text()", "for name in cfg.pop('upload',[]):files[name]={'base64':base64.b64encode((E/name).read_bytes()).decode()} if name.endswith('.xz') else (E/name).read_text()")
s=s.replace('import json,shutil\nb=Path', 'import json,shutil,base64\nb=Path').replace("p.write_text(t)\np=b/'S2W_run_host.py'", "p.write_bytes(base64.b64decode(t['base64'])) if isinstance(t,dict) else p.write_text(t)\np=b/'S2W_run_host.py'")
(E/'NKJ_run.py').write_text(s)
ref='''use super::*;
fn NKJ_add(a:u32,b:u32)->u32 {let s=a+b;if s>=P {s-P}else{s}}
pub fn NKJ_channels(q:[u32;4])->[[u32;3];3] {
 let a=NKJ_add(q[0],q[2]);let b=NKJ_add(q[1],q[3]);
 [[q[0],q[1],NKJ_add(q[0],q[1])],[q[2],q[3],NKJ_add(q[2],q[3])],[a,b,NKJ_add(a,b)]]
}
pub fn NKJ_product(a:u32,b:u32)->u64 {a as u64 * b as u64}
pub fn NKJ_row(s:[u64;3],l:[u32;3],r:[u32;3])->[u64;3] {
 [s[0]+NKJ_product(l[0],r[0]),s[1]+NKJ_product(l[1],r[1]),s[2]+NKJ_product(l[2],r[2])]
}
pub fn NKJ_accumulate(s:[[u64;3];3],l:[u32;4],r:[u32;4])->[[u64;3];3] {
 let l=NKJ_channels(l);let r=NKJ_channels(r);
 [NKJ_row(s[0],l[0],r[0]),NKJ_row(s[1],l[1],r[1]),NKJ_row(s[2],l[2],r[2])]
}
fn NKJ_words(q:QM31)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
'''
for n in [2,3,4]:
 ref+=f'pub fn NKJ_small{n}(l:[QM31;{n}],r:[QM31;{n}])->QM31 {{\n let s=NKJ_accumulate([[0;3];3],NKJ_words(l[0]),NKJ_words(r[0]));\n'
 for i in range(1,n):ref+=f' let s=NKJ_accumulate(s,NKJ_words(l[{i}]),NKJ_words(r[{i}]));\n'
 ref+=' qm31_from_karatsuba_channel_sums(s)\n}\n'
(E/'NKJ_reference.rs.txt').write_text(ref)
(E/'NKJ_prepare.py').write_text('''from pathlib import Path
import json,lzma,hashlib,subprocess,base64
B=Path(__file__).resolve().parent;S=B/'NKJ_src'
raw=lzma.decompress((B/'NKJ_FROZEN.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NKJ_FROZEN.json.sha256').read_text().strip()
pins={}
for n,t in json.loads(raw).items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t));pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
p=S/'crates/aspis-core/src/field.rs';p.write_text(p.read_text()+'\\n#[cfg(kani)]\\nmod NKJ_segments;\\nmod NKJ_reference;\\n')
(S/'crates/aspis-core/src/field/NKJ_reference.rs').write_text((B/'NKJ_reference.rs.txt').read_text())
(B/'NKJ_FROZEN_PINS.json').write_text(json.dumps(pins,indent=2))
r=subprocess.run(['patch','-p1','--forward','-i',str(B/'NKJ_KMX.patch')],cwd=S,capture_output=True,text=True)
(B/'NKJ_KMX_APPLY.log').write_text(r.stdout+r.stderr);assert r.returncode==0
print('NKJ frozen source restored, reference installed, exact KMX applied')
''')
(E/'NKJ_KMX.patch').write_bytes(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
cfg=json.loads((E/'NKJ_S001.json').read_text());cfg.update(attempt='NKJ_S002',module='NKJ_prepare',sources=['NKJ_prepare.py','NKJ_FROZEN.json.xz','NKJ_FROZEN.json.sha256','NKJ_reference.rs.txt','NKJ_KMX.patch'],upload=['NKJ_prepare.py','NKJ_FROZEN.json.xz','NKJ_FROZEN.json.sha256','NKJ_reference.rs.txt','NKJ_KMX.patch'],command=['python3','NKJ_prepare.py'],collect=['NKJ_FROZEN_PINS.json','NKJ_KMX_APPLY.log']);(E/'NKJ_S002.json').write_text(json.dumps(cfg,indent=2))
print('NKJ frozen compressed input prepared')
