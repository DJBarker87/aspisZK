"""Read/write only this lane's new-file patch archive; no repository Rust files."""
from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
def read():
 out={};name=None
 for line in (E/'NDI_harness.patch').read_text().splitlines(True):
  if line.startswith('--- '):
   assert line.strip()=='--- /dev/null';name=None
  elif line.startswith('+++ b/'):
   name=line[6:].strip();p=Path(name);assert not p.is_absolute() and '..' not in p.parts and p.name.startswith('NDI_');out[name]=''
  elif line.startswith('@@ '):pass
  elif name:
   assert line.startswith('+');out[name]+=line[1:]
 return out
def write(files):
 patch=[]
 for path,source in sorted(files.items()):
  p=Path(path);assert p.name.startswith('NDI_') and not p.is_absolute() and '..' not in p.parts
  patch+=difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/'+path)
 (E/'NDI_harness.patch').write_text(''.join(patch))
