from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-leaf-sampler1-20261027'
for rec in sorted(E.glob('LPk_K*/receipt.json')):
 a=rec.parent.name;r=json.loads(rec.read_text());patch=''
 for f in r['sources']:
  if not f.endswith('.rs'):continue
  data=subprocess.check_output(['ssh',H,'cat '+B+'/'+a+'/sources/'+f])
  assert hashlib.sha256(data).hexdigest()==r['source_hashes'][f]
  path=f.removeprefix('LPk_src/')
  orig=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],capture_output=True)
  patch+=''.join(difflib.unified_diff(orig.stdout.decode().splitlines(True),data.decode().splitlines(True),fromfile='a/'+path if orig.returncode==0 else '/dev/null',tofile='b/'+path))
 (rec.parent/'LPk_harness.patch').write_text(patch)
