"""Decode the lane's new-file-only harness patch without creating repo Rust files."""
from pathlib import Path
def files():
 out={};name=None
 for line in (Path(__file__).resolve().parent/'NDI_harness.patch').read_text().splitlines(True):
  if line.startswith('--- '):
   assert line.strip()=='--- /dev/null';name=None
  elif line.startswith('+++ b/'):
   name=line[6:].strip();assert Path(name).name.startswith('NDI_');out[name]=''
  elif line.startswith('@@ '):pass
  elif name:
   assert line.startswith('+');out[name]+=line[1:]
 return out
