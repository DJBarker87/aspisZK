from NBF_host import *
import difflib,hashlib
# Read-only receipt recovery; never submits a prover or changes host objects.
r=py(f'''from pathlib import Path
import json
b=Path({B!r});out={{}}
for a in sorted(b.glob('NBF_K[0-9]*')):
 if not a.is_dir() or not (a/'receipt.json').exists():continue
 cfg=json.loads((a/'receipt.json').read_text())
 out[a.name]={{n:(a/'sources'/n).read_text() for n in cfg['sources']}}
print(json.dumps(out))
''')
assert r.returncode==0,r.stderr
runs=json.loads(r.stdout)
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
checks={}
for a,files in runs.items():
 receipt=json.loads((E/a/'receipt.json').read_text())
 patch='';checks[a]={}
 for n,s in files.items():
  h=hashlib.sha256(s.encode()).hexdigest();assert h==receipt['source_hashes'][n],(a,n)
  name=n.removeprefix('NBF_src/')
  try:old=subprocess.check_output(['git','show',rev+':'+name],stderr=subprocess.DEVNULL,text=True)
  except subprocess.CalledProcessError:old=''
  if old!=s:
   patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
  checks[a][n]=dict(sha256=h,bytes=len(s.encode()),frozen_identical=old==s)
 (E/a/'NBF_harness.patch').write_text(patch)
(E/'NBF_ARCHIVE.json').write_text(json.dumps(checks,indent=2)+'\n')
print('Archived',len(runs),'source-hashed scratch harness patches')
