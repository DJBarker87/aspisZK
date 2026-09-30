#!/usr/bin/env python3
"""Revisit compiler layout after removing T163 and fixing the recorder frame."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
p.add_argument('--opt',choices=['2','s','z'],required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='17ab8a660db4eca296609b6b38028a30537069c45f93ad5afa88d0d8c757d808'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='5923dd9419cda40ff1274bca67823f6e0b579c1270b86d5e3fb2c3da0fc3a613'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
n='docs/research/v8-no-work-100-20260907/experiments/performance-sbf/Cargo.toml';f=dst/n;s=f.read_text()
assert s.count('opt-level = 3')==1 and 'overflow-checks = true'in s
f.write_text(s.replace('opt-level = 3','opt-level = '+('2'if a.opt=='2'else'"'+a.opt+'"')))
m['files'][n]=sha(f)
m['r97_profile']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),'opt':a.opt,
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
