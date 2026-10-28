"""Strict cumulative source reconstruction for scratch-only cfg additions."""
from pathlib import Path
import hashlib,json,tempfile,subprocess
E=Path(__file__).resolve().parent;OLD=E.parent/'native-tx2h-20261028'
def expected(request):
 base=[OLD/n for n in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_error.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']]
 own=[];seen=set()
 for p in sorted(E.glob('NBS_K[0-9][0-9][0-9]-harness.patch')):
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if h not in seen:own.append(p);seen.add(h)
 needed=hashlib.sha256(request.read_bytes()).hexdigest() not in seen
 chain=base+own
 paths=sorted(set(l[6:] for p in chain+[request] for l in p.read_text().splitlines() if l.startswith('+++ b/')))
 manifest=json.loads((OLD/'NBQ_SCRATCH_MANIFEST.json').read_text())
 with tempfile.TemporaryDirectory(prefix='NBS-cfg-sourcecheck-') as d:
  for name in paths:
   p=Path(d)/name;p.parent.mkdir(parents=True,exist_ok=True)
   r=subprocess.run(['git','show','4bb3b3f5:'+name],capture_output=True)
   if r.returncode==0:p.write_bytes(r.stdout)
   else:assert name not in manifest,('missing frozen source',name)
  def apply(p):
   r=subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,capture_output=True)
   assert r.returncode==0,(str(p),r.stderr.decode())
  for p in chain:apply(p)
  before={**manifest,**{n:hashlib.sha256((Path(d)/n).read_bytes()).hexdigest() for n in paths if (Path(d)/n).is_file()}}
  if needed:apply(request)
  after={**manifest,**{n:hashlib.sha256((Path(d)/n).read_bytes()).hexdigest() for n in paths if (Path(d)/n).is_file()}}
 return dict(before=before,after=after,apply=needed,patch_chain=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in chain+([request] if needed else [])])
