#!/usr/bin/env python3
"""Collect bounded textual receipts; keep binaries and LLBC on the build host."""
import pathlib,subprocess,json
H=pathlib.Path(__file__).resolve().parent
script='''import pathlib,json,hashlib
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref9-20261021')
result={}
for p in R.rglob('receipt.json'):
 if any(x in p.parts for x in ['source','kani-source','extraction-target','kani-target']):continue
 e=p.parent
 result[str(e.relative_to(R))]=dict(receipt=json.loads(p.read_text()),logs={n:(e/n).read_text() for n in ['stdout.log','stderr.log','time.log'] if (e/n).exists()})
result['drop-input-pins']={p.name:json.loads(p.read_text()) for p in (R/'drop').glob('*-sources.json')}
result['rust-reservations']={str(p.relative_to(R)):json.loads(p.read_text()) for p in R.rglob('*-reservation.json') if 'source' not in p.parts and 'kani-target' not in p.parts}
for e in R.glob('drop-opaque*'):
 if not e.is_dir():continue
 result[str(e.relative_to(R))+'/metadata']={p.name:json.loads(p.read_text()) for p in e.glob('*.json')}
 result[str(e.relative_to(R))+'/artifacts']={str(p.relative_to(e)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in e.rglob('*') if p.is_file() and p.suffix in ['.llbc','.lean']}
print(json.dumps(result))
'''
r=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True)
d=json.loads(r)
(H/'builder-cont9-host-evidence.json').write_text(json.dumps(d,indent=2)+'\n')
for k,v in d.items():
 if 'receipt' in v: print(k,[(x,v['receipt'][x]) for x in ['exit_status','wall_seconds','peak_rss_kib','swaps']])
