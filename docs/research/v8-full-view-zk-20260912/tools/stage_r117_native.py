#!/usr/bin/env python3
"""Retain private challenge powers across the owned final-vector fold."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='5530e93f828a38d16eb50ea651d0afaef07f40db1acf2c17af10110d99801acb'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def save(n,s):
    f=ex/n;f.write_text(s);changed.append(f)
for n in ['r117_affine.rs','r117_primal.rs']:save(n,(here/n).read_text())
f=ex/'r81_canonical_basis.rs';save(f.name,f.read_text()+'\ninclude!("r117_affine.rs");\n')
f=ex/'r17_owned_primal.rs';s=f.read_text();assert s.count('pub(super) fn fold(')==1
save(f.name,s.replace('pub(super) fn fold(','fn r117_retained_fold(')+'\ninclude!("r117_primal.rs");\n')
save('r117_primal_check.rs','''extern crate aspis_core as corelib;
use corelib::field::M31;
mod r17_owned_primal;
fn main(){r17_owned_primal::controls();}
''')
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r117-primal-check"\npath="../r117_primal_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r117_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r116_native']['fixtures'],'changed':len(set(changed))}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed))}))
