#!/usr/bin/env python3
"""Compose the source-tested R22 scalar with the complete R23 verifier."""
import argparse,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser()
for n in ['control','native','output']:p.add_argument('--'+n,type=Path,required=True)
a=p.parse_args();dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((a.control/'r18-stage.json').read_text());n=json.loads((a.native/'r18-stage.json').read_text())
assert len(m['files'])==174 and len(n['files'])==(183 if 'r24_qm' in n else 182)
for root,manifest in [(a.control,m),(a.native,n)]:
    for name,h in manifest['files'].items():assert sha(root/name)==h,name
assert not dst.exists();dst.mkdir()
for name in ['crates','docs','programs','xtask','audit']:shutil.copytree(a.control/name,dst/name,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for name in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/name).exists():(dst/name).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(a.control/name,dst/name)
ex=Path('docs/research/v8-no-work-100-20260907/experiments');changed=[]
for name in ['r19_channel_ordinary.rs','r22_scalar.rs']:
    text=(a.native/ex/name).read_text()
    text=re.sub(r'\s*super::r22_tick\("[^"]+"\);','',text)
    path=dst/ex/name;path.write_text(text);changed.append(path)
path=dst/ex/'r17_host_relation.rs';text=path.read_text()
old='let ordinary=crate::r19_channel_ordinary::terminal_shared(&public_audit,p.abc,alphas,beta,&mut workspace,&kernel);'
new='let ordinary=crate::r19_channel_ordinary::terminal_scalar(&public_audit,p.abc,alphas,beta,&core::array::from_fn(|i|finals[i]),&mut workspace,&kernel);'
assert text.count(old)==1;text=text.replace(old,new)
old='''terminal=terminal.add(corelib::field::qm31_sum_products4(
            core::array::from_fn(|i|ordinary[i].add(beta.mul(public_audit[10]).mul(sparse[i]))),
            core::array::from_fn(|i|finals[i])));'''
new='''terminal=terminal.add(ordinary).add(corelib::field::qm31_sum_products4(
            sparse,core::array::from_fn(|i|finals[i])).mul(beta.mul(public_audit[10])));'''
assert text.count(old)==1;path.write_text(text.replace(old,new));changed.append(path)
if 'r24_qm' in n:
    for name in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/r24_guarded_qm.rs']:
        shutil.copy2(a.native/name,dst/name);changed.append(dst/name)
    m['r24_qm']=n['r24_qm']
if 'r24_inactive' in n:m['r24_inactive']=n['r24_inactive']
for key in ['r24_addsub','r24_packed']:
    if key in n:m[key]=n[key]
for path in changed:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_compose']={'control_manifest_sha256':sha(a.control/'r18-stage.json'),'native_manifest_sha256':sha(a.native/'r18-stage.json'),'scalar_transpose_installed':True,'source_files':{str(p.relative_to(dst)):sha(p)for p in changed}}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
