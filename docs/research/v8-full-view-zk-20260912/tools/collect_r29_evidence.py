#!/usr/bin/env python3
"""Public source/receipt bundle; large public inverse binaries stay hash-bound on NUC."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--affine',type=Path,required=True);p.add_argument('--capacity',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--basis-lean',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output
assert not out.exists();out.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
ex='docs/research/v8-no-work-100-20260907/experiments/'
summary={'parent_revision':'5d529b7696df2eed18c2fad3ea7d078c08dc0e61','full_privacy':False,'full_soundness':False,'verifier_changed':False,'source_challenges_changed':False,'stages':{}}
for label,stage in [('affine',a.affine),('capacity',a.capacity)]:
    m=json.loads((stage/'r18-stage.json').read_text())
    for n,h in m['files'].items():assert sha(stage/n)==h,n
    copy(stage/'r18-stage.json',f'{label}/r18-stage.json');copy(stage/'r17-stage.json',f'{label}/r17-stage.json')
    selected=[ex+'r17_c1_witness_audit.rs']if label=='affine'else[ex+'r29_g_capacity.rs',ex+'r28_source_helpers.rs',ex+'performance-host/Cargo.toml']
    for n in selected:copy(stage/n,f'{label}/source/{n}')
    run=stage/('host-a'if label=='affine'else'check-a')
    for f in run.glob('*'):
        if f.suffix in['.log','.json']:copy(f,f'{label}/{f.name}')
    summary['stages'][label]={'path':str(stage),'manifest_sha256':sha(stage/'r18-stage.json'),'pins':len(m['files'])}
    if label=='affine':
        summary['stages'][label]['fixtures']=[{n:sha(run/f'fixture-world{w}'/n)for n in['public.bin','transition.bin','binding.bin','proof-1.bin']}for w in range(2)]
    else:
        for w in range(2):
            cert=run/f'world{w}/certificate.json';c=json.loads(cert.read_text());binary=run/f'world{w}/right-inverse.bin'
            assert c['sha256']==sha(binary)and c['bytes']==binary.stat().st_size
            copy(cert,f'capacity/world{w}/certificate.json');copy(stage/f'world{w}-prefix.bin',f'capacity/world{w}/prefix.bin')
for label,folder in [('lean',a.lean),('basis-lean',a.basis_lean)]:
    for f in folder.glob('*'):
        if f.suffix in['.log','.json']:copy(f,label+'/'+f.name)
(out/'receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps(summary,indent=2))
