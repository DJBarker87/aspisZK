#!/usr/bin/env python3
"""Collect the source-locked kernel reduction and focused formal receipts."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--failed-lean',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output
assert not out.exists();out.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
copy(a.stage/'r18-stage.json','r18-stage.json');copy(a.stage/'r17-stage.json','r17-stage.json')
ex='docs/research/v8-no-work-100-20260907/experiments/'
for n in [ex+'r30_kernel_separation.rs',ex+'r28_source_helpers.rs',ex+'performance-host/Cargo.toml']:copy(a.stage/n,'source/'+n)
for f in (a.stage/'check-a').rglob('*'):
    if f.is_file()and f.suffix in['.json','.log']:copy(f,'runtime/'+str(f.relative_to(a.stage/'check-a')))
for w in range(2):copy(a.stage/f'world{w}-prefix.bin',f'prefix/world{w}.bin')
for label,folder in [('lean',a.lean),('lean-root-failed',a.failed_lean)]:
    for f in folder.glob('*'):
        if f.suffix in['.log','.json']:copy(f,label+'/'+f.name)
(out/'receipt.json').write_text(json.dumps({'parent_revision':'5cf16f1796e14d8d05aa485b0a7d6ca86f5b27df','stage':str(a.stage),'source_manifest_sha256':sha(a.stage/'r18-stage.json'),'pins':len(m['files']),'source_prefix_substituted':False,'verifier_changed':False,'universal_rank_proved':False,'full_privacy':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
