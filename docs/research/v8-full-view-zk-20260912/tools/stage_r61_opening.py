#!/usr/bin/env python3
"""Re-enable the retained fixed C1 dot in the exact selected R59 workspace."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='58070ac3aa224a7ad5c55a6fa33eeb413242878e2291cc575212b3685359cb74'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==195
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
for n in ['r17-stage.json','r17-sbf-probe.json']:
    path=dst/n;meta=json.loads(path.read_text())
    assert 'v8_gamma_fixed' not in meta['rustflags'] and 'v8_gamma_fused' not in meta['rustflags']
    meta['rustflags']+=' --cfg v8_gamma_fixed';path.write_text(json.dumps(meta,indent=2)+'\n')
    m['files'][n]=sha(path)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
path=ex/'query_arithmetic.rs'
path.write_text(path.read_text()+'\n'+(here/'r61_opening_controls.rs').read_text())
check=ex/'r55_opening_check.rs';old=check.read_text();assert old.count('query_arithmetic::r55_controls();')==1
check.write_text(old.replace('query_arithmetic::r55_controls();','query_arithmetic::r55_controls();query_arithmetic::r61_controls();'))
for f in [path,check]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r61_opening']={'base_revision':'61b0a3ce324647396a9bf7e911222391e8126958','control_manifest_sha256':sha(src/'r18-stage.json'),
    'retained_fixed_dot':True,'protocol_changed':False,'validation_removed':False,'production_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
