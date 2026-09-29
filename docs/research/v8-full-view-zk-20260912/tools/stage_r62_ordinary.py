#!/usr/bin/env python3
"""Existing two-product sum on only the scalar path; keep general reference."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='088877fa9a02692519479254d348a0eebeaf379bea538b246ee8550b9ba92e8d'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==197
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
path=ex/'r19_channel_ordinary.rs';path.write_text(path.read_text()+'\n'+(here/'r62_entry.rs').read_text())
scalar=ex/'r22_scalar.rs';s=scalar.read_text()
assert s.count('entry(factors,0,SUPPORT[j])')==1 and s.count('entry(factors,0,1023)')==1 and s.count('entry(')==2
scalar.write_text(s.replace('entry(factors,0,','r62_entry(factors,'))
native=ex/'r27_native.rs';s=native.read_text();old='r19_channel_ordinary::r27_tensor_check(x);';assert s.count(old)==1
native.write_text(s.replace(old,old+'r19_channel_ordinary::r62_entry_check(x);'))
check=ex/'r27_check.rs';s=check.read_text();assert s.count('R27_SPARSE source_vectors=256')==1
check.write_text(s.replace('R27_SPARSE source_vectors=256','R62_ENTRY entry_coordinate_comparisons=262144 source_vectors=256'))
for f in [path,scalar,native,check]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r62_entry']={'base_revision':'23cf1bd882ccce6f330a4cafb6d39e54c748b984','control_manifest_sha256':sha(src/'r18-stage.json'),
    'reference_entry_unchanged':True,'scalar_sites':2,'protocol_changed':False,'validation_removed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
