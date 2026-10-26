"""Recover and validate immutable proof inputs against recorded preflight hashes."""
from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parents[3];b=Path('tools/prover-rw-20261023/pv-rw-step');e=r/'evidence/pv-rw-step-20261026'
sha=lambda x:hashlib.sha256(x).hexdigest()
known={}
for p in e.rglob('*'):
 if p.is_file():known[sha(p.read_bytes())]=p.read_bytes()
for p in (r/b).rglob('*'):
 if not p.is_file() or '__pycache__' in p.parts:continue
 data=p.read_bytes();known[sha(data)]=data
 if p.name=='lib.rs':
  t=data.decode()
  for marker in ['#[cfg(kani)]\nmod leaves','pub mod sampler_step;','#[cfg(kani)]\nmod scalar_split','#[cfg(kani)]\nmod actual_shape','#[inline(always)]\npub fn scalar_product_owned','#[cfg(kani)]\nmod matched_steps','#[cfg(kani)]\nmod matched_coordinates','pub mod parse_step;']:
   z=t.split(marker)[0].encode();known[sha(z)]=z
 if p.name=='sampler_step.rs':
  z=data.decode().split('// One complete owned')[0].encode();known[sha(z)]=z
 for rev in ['882c30be11','bbcc13a0af']:
  z=subprocess.run(['git','show',f'{rev}:{p.relative_to(r)}'],cwd=r,capture_output=True)
  if not z.returncode:known[sha(z.stdout)]=z.stdout
rows=[]
for f in sorted(e.glob('pv-rw-step-*/preflight.json')):
 x=json.loads(f.read_text());missing=[];retained=[]
 for name,digest in x['source_sha256'].items():
  if not name.startswith(str(b)) or Path(name).suffix not in ['.rs','.toml','.py']:continue
  if digest not in known:missing.append(name);continue
  dst=f.parent/'inputs'/Path(name).relative_to(b);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(known[digest]);retained.append(name)
 rows.append(dict(attempt=f.parent.name,retained=retained,missing=missing))
(e/'input-snapshots.json').write_text(json.dumps(rows,indent=2)+'\n')
print('snapshots',len(rows),'missing',[(x['attempt'],x['missing']) for x in rows if x['missing']])
assert not any(x['missing'] for x in rows)
