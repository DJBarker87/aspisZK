#!/usr/bin/env python3
"""Keep guarded raw product formula; delay only checked-dot final reductions."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='e24eedc1c69eb9d251a13df9d2d48339a5bacb32ece9ddf6ba0fdbbf2fcc02f2'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==195
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src';raw=(field/'r24_guarded_qm.rs').read_text()
assert raw==(here/'r56_partial_product.rs').read_text()
raw=raw.replace('fn r24_canonical_mul(left:QM31,right:QM31)->Option<QM31>', 'fn r59_raw_product(left:QM31,right:QM31)->Option<[u64;4]>')
old='].map(M31::reduce_u64);\n    Some(QM31{c0:CM31::new(out[0],out[1]),c1:CM31::new(out[2],out[3])})'
assert raw.count(old)==1;raw=raw.replace(old,'];\n    Some(out)')
helper=field/'r25_checked_dot.rs';helper.write_text('// Raw outputs stay private to this checked dot.\n'+raw+'\n'+(here/'r59_partial_dot.rs').read_text())
m['files'][str(helper.relative_to(dst))]=sha(helper)
m['r59_partial_dot']={'base_revision':'6af7c8384ccea9dce41e16075cd29f77179bd8a0','control_manifest_sha256':sha(src/'r18-stage.json'),
    'input_guards_unchanged':True,'raw_formula_unchanged':True,'four_accumulators':True,'max_terms':4096,'protocol_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
