#!/usr/bin/env python3
"""Finish a fresh R21 stage with one generated circuit and bounded pilot targets."""
import argparse,hashlib,json,shutil
from pathlib import Path
EX=Path('docs/research/v8-no-work-100-20260907/experiments')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--circuit',type=Path,required=True);p.add_argument('--native',action='store_true');a=p.parse_args()
m=json.loads((a.stage/'r18-stage.json').read_text());assert 'r21_pilot' in m and 'r21_circuit' not in m
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
here=Path(__file__).parent;changed=[]
for n,src in [('r21_circuit.rs',a.circuit/'r21_circuit.rs'),('r21_pilot.rs',here/'r21_pilot.rs'),('r21_sbf.rs',here/'r21_sbf.rs')]:
    dest=a.stage/EX/n;assert not dest.exists();shutil.copy2(src,dest);changed.append(dest)
dest=a.stage/EX/'performance-host/Cargo.toml'
dest.write_text(dest.read_text()+'\n[[bin]]\nname="r21-pilot"\npath="../r21_pilot.rs"\n');changed.append(dest)
dest=a.stage/EX/'performance-sbf/Cargo.toml';text=dest.read_text();assert text.count('path = "../relation_callback.rs"')==1
dest.write_text(text.replace('path = "../relation_callback.rs"','path = "../r21_sbf.rs"'));changed.append(dest)
for dest in changed:m['files'][str(dest.relative_to(a.stage))]=sha(dest)
m['r21_circuit']={'profile':json.loads((a.circuit/'circuit-profile.json').read_text()),'native_control':a.native,'full_aspis_verifier':False,'source_files':{str(p.relative_to(a.stage)):sha(p)for p in changed}}
(a.stage/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
probe=json.loads((a.stage/'r17-sbf-probe.json').read_text())
if a.native:probe['rustflags']+=' --cfg r21_native_control'
probe['r21_scope']='ordinary+image pilot ONLY';(a.stage/'r17-sbf-probe.json').write_text(json.dumps(probe,indent=2)+'\n')
print(json.dumps({'circuit_id':m['r21_circuit']['profile']['circuit_id'],'proof_bytes':m['r21_circuit']['profile']['proof_bytes'],'native':a.native,'built':False}))
