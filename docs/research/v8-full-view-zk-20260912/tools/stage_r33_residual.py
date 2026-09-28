#!/usr/bin/env python3
"""Stage the source residual experiment without touching verifier paths."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--prefixes',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==187 and 'r31_inverse'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists()and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';path=ex/'r33_g_residual.rs';shutil.copy2(here/path.name,path)
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r33-g-residual"\npath="../r33_g_residual.rs"\n')
for f in[path,cargo]:m['files'][str(f.relative_to(dst))]=sha(f)
for w in range(2):
    prefix=a.prefixes/f'world{w}-prefix.bin';assert sha(prefix)==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256'];shutil.copy2(prefix,dst/prefix.name)
m['r33_residual']={'base_revision':'ff6056e5596470c7b473d316e599a37f5fa837aa','control_manifest_sha256':sha(src/'r18-stage.json'),'selected_columns':271,'free_columns':428,'residual_rows':17,'verifier_changed':False,'source_prefix_substituted':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
