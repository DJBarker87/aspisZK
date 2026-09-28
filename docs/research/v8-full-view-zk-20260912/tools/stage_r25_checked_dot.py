#!/usr/bin/env python3
"""Source-exact checked-dot boundary experiment on the selected R24 control."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==179 and 'r24_simple_dot' in m and 'r24_reconstruct' in m and 'r24_inline' not in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists() and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
field=dst/'crates/aspis-core/src/field.rs';field.write_text(field.read_text()+'\ninclude!("r25_checked_dot.rs");\n')
helper=field.parent/'r25_checked_dot.rs';shutil.copy2(here/helper.name,helper)
adapter=dst/'docs/research/v8-no-work-100-20260907/experiments/r20_private_dot_adapter.rs'
adapter.write_text('''//! Checked dot boundary, preserving length and every canonicality check.
use aspis_core::field::QM31 as K;
#[inline(never)]
pub(super) fn dot(left:&[K],right:&[K])->Option<K> {
    aspis_core::field::r25_checked_dot(left,right)
}
''')
for path in [field,helper,adapter]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r25_checked_dot']={'control_manifest_sha256':sha(src/'r18-stage.json'),'canonical_validation_retained':True,'public_general_field_api_unchanged':True,'max_terms':4096,'new_checked_helper':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
