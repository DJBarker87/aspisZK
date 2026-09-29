#!/usr/bin/env python3
"""Stage fixed-arity source without array-map/iterator dependencies.
This is a real execution candidate, not an extraction-only normalization.
"""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='10187c96f6d4549f334aefc477f17899f4e2af8004e2cbd993380382f5fdefc2'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==197
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
ref=ex/'r69_reference';ref.mkdir();changed=[]
for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    shutil.copy2(src/'crates/aspis-core/src'/n,ref/n);changed.append(ref/n)
helper=dst/'crates/aspis-core/src/r24_guarded_qm.rs'
shutil.copy2(here/'r69_explicit_product.rs',helper);changed.append(helper)
test=ex/'r69_explicit_check.rs';shutil.copy2(here/test.name,test);changed.append(test)
cargo=ex/'performance-host/Cargo.toml'
cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r69-explicit-check"\npath="../r69_explicit_check.rs"\n');changed.append(cargo)
for path in changed:m['files'][str(path.relative_to(dst))]=sha(path)
assert len(m['files'])==202
m['r69_explicit_product']={
    'base_revision':'265a251ecfbff6cd971a32eccd72cff552786885',
    'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,
    'purpose':'fixed-arity source removes unmodeled iterator/map dependencies; test before selection'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
