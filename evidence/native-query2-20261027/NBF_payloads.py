"""Read scratch-only harness text from retained review patches, never shipped files."""
from pathlib import Path
E=Path(__file__).resolve().parent

def read_payload(name):
 p=E/(name+'.txt')
 if p.is_file():return p.read_text()
 target='crates/aspis-r1-cost-probe/src/'+name
 active=False;out=[]
 for line in (E/'NBF_harness.patch').read_text().splitlines(keepends=True):
  if line.startswith('--- '):active=False
  elif line.startswith('+++ '):active=line.rstrip()=='+++ b/'+target
  elif active and line.startswith('+'):out.append(line[1:])
 if not out:raise FileNotFoundError(target+' absent from review patch')
 return ''.join(out)
