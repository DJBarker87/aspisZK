#!/usr/bin/env python3
"""Stream the actual sparse terminal with existing private arithmetic."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='85d6a0e50d4106fadf525ffa52cf617139623a7190120e376d812835655eeb53'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='c3f1b2e99bb29def6161b59cfc0ad6ecd2e1dd836bfb826e80b9dfe57c8d7e97'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
f=ex/'r81_canonical_basis.rs';f.write_text(f.read_text()+'\n'+(here/'r92_private_dot.rs').read_text());changed.append(f)
f=ex/'r22_scalar.rs';s=f.read_text()
needle='pub(super) fn r81_sparse_scalar_after_ordinary(';assert s.count(needle)==1
s=s.replace(needle,'pub(super) fn r92_sparse_retained(',1)
needle='    assert_eq!(r81_sparse_scalar_after_ordinary(&coins,&workspace,&kernel),expected,'
assert s.count(needle)==1
s=s.replace(needle,'    assert_eq!(r92_sparse_retained(&coins,&workspace,&kernel),expected);\n'+needle)
f.write_text(s+'\n'+(here/'r92_sparse.rs').read_text());changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r92_sparse']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
