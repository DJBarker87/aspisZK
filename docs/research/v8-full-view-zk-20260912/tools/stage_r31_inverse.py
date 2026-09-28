#!/usr/bin/env python3
"""Add only a host checker to the fully pinned R30 source workspace."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==186 and 'r30_kernel'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists()and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';path=ex/'r31_sparse_g_inverse.rs';shutil.copy2(here/path.name,path)
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r31-sparse-g-inverse"\npath="../r31_sparse_g_inverse.rs"\n')
for f in[path,cargo]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r31_inverse']={'base_revision':'331866cfbe3269add68e9ce7c8e050a5e96fdfaa','control_manifest_sha256':sha(src/'r18-stage.json'),'selected_columns':271,'algebraic_witness_only':True,'verifier_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
