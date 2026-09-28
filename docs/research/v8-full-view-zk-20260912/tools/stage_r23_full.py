#!/usr/bin/env python3
"""Frozen complete R20 verifier + the two tested guarded product sites only."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser()
for n in ['control','candidate','output']:p.add_argument('--'+n,type=Path,required=True)
a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==173
c=json.loads((a.candidate/'r18-stage.json').read_text());assert c['r23_width']['rewrite_sites']==2
for root,manifest in [(src,m),(a.candidate,c)]:
    for n,h in manifest['files'].items():assert sha(root/n)==h,n
assert sha(src/'crates/aspis-core/src/field.rs')==c['r23_width']['original_field_sha256']
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
for n in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/r23_width.rs']:
    shutil.copy2(a.candidate/n,dst/n);m['files'][n]=sha(dst/n)
m['r23_width']=dict(c['r23_width'],scope='complete R20 verifier; R22 scalar NOT integrated',control_manifest_sha256=sha(src/'r18-stage.json'))
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'scope':m['r23_width']['scope']}))
