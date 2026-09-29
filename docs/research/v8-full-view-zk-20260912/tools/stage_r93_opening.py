#!/usr/bin/env python3
"""Test complete mixed-width limb outlining, not generic multiplication inlining."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='fc8723321e919f51abdf4b0ab9d4d60ea84c66afc2a94869f35406827df44f9a'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='5ff291f6956eb58653a3fceea8b0e9e5f51de2088593ce1fe78763b5f26d0e17'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
n='docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs';f=dst/n;s=f.read_text()
needle='#[inline(always)]\nfn r83_mixed_limb';assert s.count(needle)==1
f.write_text(s.replace(needle,'#[inline(never)]\nfn r83_mixed_limb'));m['files'][n]=sha(f)
m['r93_opening']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
