#!/usr/bin/env python3
"""Keep only public certificates, source pins and bounded-run receipts."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--capacity',type=Path,required=True);p.add_argument('--affine',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output
assert not out.exists();out.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
summary={'parent_revision':'1106f4586fa7296d721dcbb115627fe811dc0621','full_privacy':False,'full_soundness':False,'verifier_changed':False,'source_beta_changed':False,'stages':{}}
ex='docs/research/v8-no-work-100-20260907/experiments/'
for label,stage in [('capacity',a.capacity),('affine',a.affine)]:
    m=json.loads((stage/'r18-stage.json').read_text())
    for n,h in m['files'].items():assert sha(stage/n)==h,n
    copy(stage/'r18-stage.json',f'{label}/r18-stage.json')
    copy(stage/'r17-stage.json',f'{label}/r17-stage.json')
    for n in [ex+'r28_h1_capacity.rs',ex+'r28_source_helpers.rs',ex+'performance-host/Cargo.toml',ex+'r17_c1_witness_audit.rs',ex+'performance.rs']:
        copy(stage/n,f'{label}/source/{n}')
    check=stage/('check-b'if label=='capacity'else'host-a')
    for f in sorted(check.glob('*')):
        if f.suffix in ['.log','.json']:copy(f,f'{label}/{f.name}')
    summary['stages'][label]={'path':str(stage),'manifest_sha256':sha(stage/'r18-stage.json'),'pins':len(m['files'])}
    if label=='capacity':
        for w in range(2):
            copy(stage/f'world{w}-prefix.bin',f'capacity/world{w}/prefix.bin')
            for n in ['right-inverse.bin','targets.bin']:copy(check/f'world{w}'/n,f'capacity/world{w}/{n}')
    else:
        fixtures=[]
        for w in range(2):
            fixture=check/f'fixture-world{w}'
            fixtures.append({n:sha(fixture/n)for n in ['public.bin','transition.bin','binding.bin','proof-1.bin']})
        summary['stages'][label]['fixtures']=fixtures
for f in a.lean.iterdir():
    if f.suffix in ['.log','.json']:copy(f,'lean/'+f.name)
failed=a.capacity.parent/'aspis-r28-h1-capacity-20260928-a/check-a/compile.log';copy(failed,'failed-import/compile.log')
(out/'receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps(summary,indent=2))
