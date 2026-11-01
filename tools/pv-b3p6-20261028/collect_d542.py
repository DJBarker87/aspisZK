"""Collect each existing receipt exactly once; no build or resubmission."""
from pathlib import Path
import subprocess,tarfile
H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028';D=Path('evidence/pv-b3p6-20261028/resume17')
p=subprocess.Popen(['ssh','dombarker@100.108.41.90','tar','-C',H,'-cf','-','-T','resume17/D542-collect-paths.txt'],stdout=subprocess.PIPE)
with tarfile.open(fileobj=p.stdout,mode='r|')as t:
 for a in t:
  assert a.isfile(),a.name
  name=a.name.removeprefix('resume17/');q=D/name
  assert q.resolve().is_relative_to(D.resolve()),a.name
  q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(t.extractfile(a).read())
assert p.wait()==0
