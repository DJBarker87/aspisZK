#!/usr/bin/env python3
"""Extend the winning norm path through the final QM31-by-CM31 product."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='3110e00bcdd4e842052fe5447d0d5cbfa986f9c6c41104d2646574e22750b660'
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
save('r112_complex.rs',(here/'r112_complex.rs').read_text())
f=ex/'r81_canonical_basis.rs';save(f.name,f.read_text()+'\ninclude!("r112_complex.rs");\n')
f=ex/'r99_fold_inverse.rs';s=f.read_text()
for old,new in [('->Option<[K;4]>','->Option<[CQ;4]>'),
 ('Some([positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)].map(output))','Some([positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)])'),
 ('let ni=norms[4*i+j];out.push(K{c0:v.c0.mul(ni),c1:v.c1.mul(ni)});','let ni=norms[4*i+j];out.push(output(v.mul_complex(ni.a.0,ni.b.0).ok_or(Error::Domain)?));')]:
    assert s.count(old)==1,(f.name,old);s=s.replace(old,new)
save(f.name,s)
f=ex/'r110_norm_check.rs';s=f.read_text();assert s.count('fn main(){')==1
save('r112_norm_check.rs','#[path="r81_canonical_basis.rs"]mod r112_private;\n'+s.replace('fn main(){','fn main(){r112_private::r112_controls();'))
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r112-norm-check"\npath="../r112_norm_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r112_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r110_native']['fixtures'],'changed':len(set(changed))}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed))}))
