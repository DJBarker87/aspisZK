"""Reconstruct every own changed source byte from frozen source and exact patches."""
from pathlib import Path
import subprocess,hashlib,tempfile,json
E=Path(__file__).resolve().parent; OLD=E.parent/'native-tx2r-20261028'
# Only these scratch paths may differ from the release; no source replacement.
def expected(request):
 chain=[];seen=set()
 for p in sorted(OLD.glob('NCI_K[0-9][0-9][0-9]-harness.patch'))+sorted(E.glob('NCN_K[0-9][0-9][0-9]-harness.patch')):
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if h not in seen:chain.append(p);seen.add(h)
 needed=hashlib.sha256(request.read_bytes()).hexdigest() not in seen
 paths=sorted(set(l[6:] for p in chain+[request] for l in p.read_text().splitlines() if l.startswith('+++ b/')))
 with tempfile.TemporaryDirectory(prefix='NCI-check-') as d:
  for name in paths:
   p=Path(d)/name;p.parent.mkdir(parents=True,exist_ok=True)
   r=subprocess.run(['git','show','4bb3b3f5:'+name],capture_output=True)
   if r.returncode==0:p.write_bytes(r.stdout)
  def apply(p):
   r=subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,capture_output=True)
   assert r.returncode==0,(str(p),r.stderr.decode())
  for p in chain:apply(p)
  before={n:hashlib.sha256((Path(d)/n).read_bytes()).hexdigest() for n in paths if (Path(d)/n).is_file()}
  if needed:apply(request)
  after={n:hashlib.sha256((Path(d)/n).read_bytes()).hexdigest() for n in paths if (Path(d)/n).is_file()}
 return dict(before=before,after=after,apply=needed,patch_chain=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in chain+([request] if needed else [])])
