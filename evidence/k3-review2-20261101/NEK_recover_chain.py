from NEK_scan import *
import sys,tempfile
from pathlib import Path
rp=sys.argv[1];receipt=read_json(ROOT/rp);bases={};steps=[]
for item in receipt['deps_fingerprint']['cfg_patch_chain']:
 path=item['path'].split('/evidence/',1)[1];path='evidence/'+path
 p=ROOT/path;b=p.read_bytes() if p.exists() else subprocess.check_output(['git','show','HEAD:'+path]);assert sha(b)==item['sha256'],path
 changed=dict(patched_files(b.decode(),bases));bases.update(changed);steps.append(dict(path=path,sha256=sha(b),outputs={n:sha(t.encode()) for n,t in changed.items()}))
print('steps',len(steps),'files',len(bases))
want=receipt['source_hashes'];matches={n:t for n,t in bases.items() if any(k.endswith('/'+n) and h==sha(t.encode()) for k,h in want.items())}
# git apply preserves context while permitting historical line offsets; the
# final receipt SHA is mandatory. The scanner's stricter offset parser can miss
# otherwise exact chains after a prior inserted hunk shifts a later hunk.
with tempfile.TemporaryDirectory(prefix='NEK-chain-') as td:
 names=set()
 patch_inputs=[]
 for item in receipt['deps_fingerprint']['cfg_patch_chain']:
  path='evidence/'+item['path'].split('/evidence/',1)[1];p=ROOT/path;b=p.read_bytes() if p.exists() else subprocess.check_output(['git','show','HEAD:'+path]);patch_inputs.append((path,b))
  names.update(l[6:] for l in b.decode().splitlines() if l.startswith('+++ b/'))
 for n in names:
  b=frozen(n)
  if b is not None:q=Path(td)/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 for path,b in patch_inputs:
  r=subprocess.run(['git','apply','-'],input=b,cwd=td,capture_output=True)
  assert r.returncode==0,(path,r.stderr.decode())
 for n in names:
  p=Path(td)/n
  if p.exists() and any(k.endswith('/'+n) and h==sha(p.read_bytes()) for k,h in want.items()):matches[n]=p.read_text()
name=Path(rp).parent.name
(E/('NEK_'+name+'_chain.json.xz')).write_bytes(lzma.compress(json.dumps(matches,sort_keys=True).encode()))
(E/('NEK_'+name+'_chain_steps.json')).write_text(json.dumps(steps,indent=2)+'\n')
print('matched',list(matches))
