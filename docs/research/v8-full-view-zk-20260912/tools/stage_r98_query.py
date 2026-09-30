#!/usr/bin/env python3
"""Expose the actual public query guard to extraction without opaque ctpop."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='17ab8a660db4eca296609b6b38028a30537069c45f93ad5afa88d0d8c757d808'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
f=dst/'crates/aspis-core/src/transcript.rs';old=f.read_text();needle='        if !bound.is_power_of_two() {';assert old.count(needle)==1
f.write_text(old.replace(needle,'        if bound == 0 || (bound & (bound - 1)) != 0 {'));changed.append(f)
f=ex/'r98_reference_transcript.rs';shutil.copy2(src/'crates/aspis-core/src/transcript.rs',f);changed.append(f)
f=ex/'r98_query_check.rs';shutil.copy2(here/f.name,f);changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r98-query-check"\npath="../r98_query_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r98_query']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
 'rewrite':'Short-circuit zero test then x & (x-1); reject exactly non-powers of two.'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
