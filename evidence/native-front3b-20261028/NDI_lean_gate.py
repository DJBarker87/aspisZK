"""Lane-owned stricter dependency validation; unchanged shared launcher."""
from pathlib import Path
import hashlib,json,subprocess,sys
B=Path(__file__).resolve().parent
x=json.loads((B/sys.argv[1]).read_text())
def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
errors=[];objects=dict(x['deps_fingerprint']['selected_objects'])
if x['deps_fingerprint'].get('extra_pinset_sha256'):
 p=B/'NDI_EXTRA_PINS.json';assert sha(p)==x['deps_fingerprint']['extra_pinset_sha256']
 extra=json.loads(p.read_text())['selected_objects']
 for path,pin in extra.items():
  if path in objects:assert objects[path]['sha256']==pin['sha256']
  objects[path]=pin
for path,pin in objects.items():
 if sha(path)!=pin['sha256']:errors.append(path)
for path,pin in x['deps_fingerprint'].get('own_sources',{}).items():
 if sha(path)!=pin:errors.append(path)
(B/(x['attempt']+'-dependency-check.json')).write_text(json.dumps(dict(objects=len(objects),own_sources=len(x['deps_fingerprint'].get('own_sources',{})),errors=errors),indent=2)+'\n')
assert not errors,('STOP pinned dependency changed',errors)
sys.exit(subprocess.run(x['lean_command'],cwd=B).returncode)
