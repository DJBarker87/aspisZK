"""Recover lane-owned Rust inputs from source-only patches."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
def sources():
 out={};name=None
 for line in (E/'NDL_HARNESS_INPUTS.patch').read_text().splitlines(True):
  if line.startswith('--- '):assert line.strip()=='--- /dev/null';name=None
  elif line.startswith('+++ b/'):name=line[6:].strip();assert name.startswith('NDL_') and '/' not in name;out[name]=''
  elif line.startswith('@@ '):pass
  elif name:assert line.startswith('+');out[name]+=line[1:]
 pins=json.loads((E/'NDL_HARNESS_INPUTS.json').read_text())
 assert set(out)==set(pins)
 assert all(hashlib.sha256(v.encode()).hexdigest()==pins[n] for n,v in out.items())
 return out
def source(name):
 p=E/name
 return p.read_text() if p.exists() else sources()[name]
