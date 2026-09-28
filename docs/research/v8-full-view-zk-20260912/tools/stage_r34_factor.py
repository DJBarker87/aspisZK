#!/usr/bin/env python3
"""Extend the pinned R33 host workspace; production paths remain unchanged."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((a.control/'r18-stage.json').read_text());assert len(m['files'])==188
for n,h in m['files'].items():assert sha(a.control/n)==h,n
assert not a.output.exists();a.output.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(a.control/n,a.output/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(a.output/n).exists():(a.output/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(a.control/n,a.output/n)
ex=a.output/'docs/research/v8-no-work-100-20260907/experiments';f=ex/'r34_low_factor.rs';shutil.copy2(Path(__file__).with_name(f.name),f)
c=ex/'performance-host/Cargo.toml';c.write_text(c.read_text()+'\n[[bin]]\nname="r34-low-factor"\npath="../r34_low_factor.rs"\n')
for f in[f,c]:m['files'][str(f.relative_to(a.output))]=sha(f)
for w in range(2):
    f=a.control/f'world{w}-prefix.bin';assert sha(f)==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256'];shutil.copy2(f,a.output/f.name)
    f=a.control/f'check-a/world{w}/residual-minor.bin';shutil.copy2(f,a.output/f'world{w}-minor.bin')
m['r34_factor']={'base_revision':'03549062720acd4fe4ca87f1eac82391e069f2ca','control_manifest_sha256':sha(a.control/'r18-stage.json'),'verifier_changed':False}
(a.output/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'pins':len(m['files'])}))
