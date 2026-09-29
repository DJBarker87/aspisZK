#!/usr/bin/env python3
"""Restore the retained Merkle-input winner on the exact R85 source/proofs.

The older patch and its tests are reused, not re-derived. Only a task-owned
source overlay changes. SHA backends must hash concatenated slice bytes.
"""
import argparse, hashlib, json, shutil, subprocess
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='018879a442490fe9ba4b495be8dbb767254f8f985168660be752b4e917ccafea'
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='fb467f0084aadec72cbe581e92f801622998566afbe62525b5e70eb2f4defe50'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert m['r85_native']['variant']=='compose' and not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
patch=ex/'merkle-input.patch'
assert sha(patch)=='ea39d16fdab7717d631cca24191d44174e89765e71a4b32ee31a3d00adb2448f'
assert sha(ex/'merkle_input_tests.rs')=='ba737c605bcac98ee86473365612618369eb768f564dc1b130e932369dff0226'
assert sha(ex/'leaf_record.rs')=='f38d7070d4a3d924f1dd8ecf884db48edb66eb2c27ea5e5aea7f1c46286ca998'
# --check prevents partially applied/mismatched source overlays.
for extra in [['--check'],[]]:
    subprocess.run(['git','apply','--recount',*extra,str(patch)],cwd=dst,check=True)
changed=[dst/'crates/aspis-core/src/v7_merkle208.rs']
for name in ['r17-stage.json','r17-sbf-probe.json']:
    f=dst/name;v=json.loads(f.read_text())
    assert 'v8_merkle_slices' not in v['rustflags']
    v['rustflags']+=' --cfg v8_merkle_slices --cfg v8_merkle_borrow --cfg v8_leaf_record'
    f.write_text(json.dumps(v,indent=2)+'\n');changed.append(f)
f=ex/'r17_host_relation.rs';s=f.read_text()
start=s.index('pub(super) fn opened_channel(');end=s.index('// New-profile verifier suffix.',start)
part=s[start:end];needle='private_leaf_hash_v7(hash, V7_C2_TREE_TAG, &r[403..589], salt),'
assert part.count(needle)==1
part=part.replace(needle,'leaf_record::c2(hash, r),')
f.write_text(s[:start]+part+s[end:]);changed.append(f)
f=ex/'r86_leaf_check.rs';shutil.copy2(here/f.name,f);changed.append(f)
f=ex/'performance-host/Cargo.toml'
f.write_text(f.read_text()+'\n[[bin]]\nname="r86-leaf-check"\npath="../r86_leaf_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r86_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'variant':'retained-merkle-inputs-and-c2-record','protocol_changed':False,
    'validation_removed':False,'new_security_claim':False,'selected':False,
    'reused_patch_sha256':sha(patch),'reused_tests_sha256':sha(ex/'merkle_input_tests.rs')}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'variant':m['r86_native']['variant']}))
