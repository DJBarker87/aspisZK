"""Remove only verified private compiler caches after all release gates pass."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd7-20261102')
assert D.resolve()==D and not D.is_symlink()
for n in [90797,90798,90799]:
 t=(D/f'lean-{n}/time.log').read_text()
 assert 'Exit status: 0' in t,n
assert json.load(open(D/'coherence-result.json'))['status'].startswith('PASS')
assert (D/'raw-audit').is_dir() and (D/'lean-sources').is_dir()
rows=[]
for name in ['lean-objects','external-objects']:
 p=D/name;assert p.is_dir() and not p.is_symlink()
 for f in p.rglob('*'):
  assert not f.is_symlink(),f
  if f.is_file():
   assert any(x in f.name for x in ['.olean','.ilean','.ir','.hash','.trace','.c','.o','.so']),f
   assert not any(x in f.name.lower() for x in ['wallet','keypair','.pem','.key']),f
   rows.append(dict(path=str(f.relative_to(D)),size=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
# Complete inventory succeeds before either cache is removed. Sources, evidence,
# audit outputs, manifests, configuration, and any keys are never cleanup paths.
for name in ['lean-objects','external-objects']:shutil.rmtree(D/name)
result=dict(status='PASS',removed_directories=['lean-objects','external-objects'],files=len(rows),bytes=sum(x['size'] for x in rows),inventory=rows,preserved=['lean-sources','raw-audit','all scope receipts','all manifests and configuration'],keys_touched=False)
(D/'cleanup-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('Removed private compiler caches:',result['files'],'files;',result['bytes'],'bytes; all sources/evidence retained')
