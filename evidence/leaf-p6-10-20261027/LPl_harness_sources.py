"""Recover owned harness text from its committed patch, without a Rust tree."""
from pathlib import Path
import re

def sources(patch: Path):
 out={}
 for part in re.split(r'(?=^--- )',patch.read_text(),flags=re.M):
  if not part:continue
  lines=part.splitlines(True)
  if lines[0].strip()!='--- /dev/null':continue
  target=lines[1].strip().removeprefix('+++ b/')
  name=Path(target).name
  if not name.startswith('LPl_') or not name.endswith('.rs'):continue
  assert target=='crates/aspis-r1-cost-probe/src/'+name,target
  out[name]=''.join(l[1:] for l in lines[2:] if l.startswith('+')).encode()
 return out
