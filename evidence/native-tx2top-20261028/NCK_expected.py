"""Validate every frozen source and exact cumulative scratch patch before launch."""
from pathlib import Path
import hashlib,json,tempfile,subprocess
E=Path(__file__).resolve().parent

def expected(request):
 manifest=json.loads((E/'NCK_FROZEN_MANIFEST.json').read_text())
 kmx=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'
 initial=E/'NCK_native.patch'
 assert request.name in ['NCK_native.patch','NCK_split.patch']
 prefix=[] if request.name=='NCK_native.patch' else [kmx,initial]
 suffix=[kmx,initial] if request.name=='NCK_native.patch' else [request]
 patches=prefix+suffix
 paths=sorted(set(l[6:] for p in patches for l in p.read_text().splitlines() if l.startswith('+++ b/')))
 with tempfile.TemporaryDirectory(prefix='NCK-sourcecheck-') as d:
  for n in paths:
   r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True)
   if r.returncode==0:
    p=Path(d)/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(r.stdout)
   else:assert n not in manifest
  def apply(p):
   r=subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,capture_output=True)
   assert r.returncode==0,(str(p),r.stderr.decode())
  def state():return {**manifest,**{n:hashlib.sha256((Path(d)/n).read_bytes()).hexdigest() for n in paths if (Path(d)/n).is_file()}}
  for p in prefix:apply(p)
  before=state()
  for p in suffix:apply(p)
  after=state()
 return dict(before=before,after=after,apply=True,patch_chain=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in patches],combined_patch=''.join(p.read_text() for p in suffix))
