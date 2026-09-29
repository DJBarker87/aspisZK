#!/usr/bin/env python3
"""Execution-layout experiment only; no field or authenticated-byte change."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='ddece23bc284c96ef9fc1d2e973701af7c2fdb347529941cd2bf7daf911c749a'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='95fbbdf3ed3acb9bd8fda2e8a130bad22e1ae14b58d9147f45044ef24ab3df94'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
f=dst/'crates/aspis-core/src/field.rs';s=f.read_text()
assert s.count('pub struct CM31 {')==1
s=s.replace('pub struct CM31 {','#[repr(align(8))]\npub struct CM31 {')
s+='''
// R88 layout-only experiment: sizes and wire serialization stay unchanged.
const _:()={
    assert!(core::mem::size_of::<M31>()==4);
    assert!(core::mem::size_of::<CM31>()==8);
    assert!(core::mem::size_of::<QM31>()==16);
    assert!(core::mem::align_of::<CM31>()==8);
    assert!(core::mem::align_of::<QM31>()==8);
};
'''
f.write_text(s);changed.append(f)
for name in ['r81_canonical_basis.rs','r20_private_canonical.rs']:
    f=ex/name;s=f.read_text();assert s.count('pub struct Q([u32;4]);')==1
    s=s.replace('pub struct Q([u32;4]);','#[repr(align(8))]\npub struct Q([u32;4]);')
    s+='\nconst _:()={assert!(core::mem::size_of::<Q>()==16);assert!(core::mem::align_of::<Q>()==8);};\n'
    f.write_text(s);changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r88_alignment']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
    'sizes_unchanged':True,'arithmetic_bodies_unchanged':True,'wire_decoding_unchanged':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'field_alignment':8}))
