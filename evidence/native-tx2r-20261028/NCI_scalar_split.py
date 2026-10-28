from pathlib import Path
from NCI_extend import extend
import subprocess,difflib,tempfile,hashlib
E=Path(__file__).resolve().parent
# Reconstruct the exact source using the same checked patch chain.
chain=[];seen=set()
for p in sorted(E.glob('NCI_K[0-9][0-9][0-9]-harness.patch')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h not in seen:chain.append(p);seen.add(h)
paths=set(l[6:] for p in chain for l in p.read_text().splitlines() if l.startswith('+++ b/'))
with tempfile.TemporaryDirectory(prefix='NCI-split-') as d:
 for n in paths:
  r=subprocess.run(['git','show','4bb3b3f5:'+n],capture_output=True)
  if r.returncode==0:
   p=Path(d)/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(r.stdout)
 for p in chain:subprocess.run(['git','apply','-'],input=p.read_bytes(),cwd=d,check=True)
 n='crates/aspis-r1-cost-probe/src/verifier.rs';s=(Path(d)/n).read_text()
 start=s.index('#[cfg(kani)] mod NCI_scalars')
 new=s[:start]+s[start:].replace('[u8;1768]','[u8;64]').replace('start<=1736','start<=32').replace('r.bytes.len()==1768','r.bytes.len()==64')
 (E/'NCI_scalar_window.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
