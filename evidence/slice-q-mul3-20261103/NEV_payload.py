"""Own payload writer; changes remain cfg(kani) additions in private scratch."""
from pathlib import Path
import json,difflib
E=Path(__file__).resolve().parent
def write(x):
 (E/'NEV_PAYLOAD.json').write_text(json.dumps(x))
 frozen=json.loads((E/'NEV_FROZEN.json').read_text());patch=''
 for name,text in x.items():
  if name.endswith('.lean'):continue
  patch+=''.join(difflib.unified_diff(frozen.get(name,'').splitlines(True),text.splitlines(True),fromfile='a/'+name,tofile='b/'+name))
 (E/'NEV_native.patch').write_text(patch)
