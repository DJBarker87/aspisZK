#!/usr/bin/env python3
"""Collect continuation-4 host receipts and logs, never objects or binaries."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent
DEST=HERE/'builder-cont4-evidence'
script=r'''import pathlib,hashlib,json,re
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021')
E=R/'continuation4'
r={}
for p in sorted(E.rglob('*')):
 if not p.is_file():continue
 if p.suffix in ['.json','.jsonl','.log']:
  raw=p.read_text(errors='replace')
  key=str(p.relative_to(E))
  if p.suffix=='.log' and len(raw)>16000:
   r[key+'.full-host-pin']=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size,host_path=str(p))
   if 'Thread ' in raw:
    first=raw.index('Thread ')
    mark=raw.rfind('warning: Found the following unsupported constructs:',0,first)
    prefix=raw[mark:first] if mark>=0 else ''
    raw='[Compiler warnings condensed; complete log is pinned on host.]\n'+prefix+raw[first:]
   else:
    raw='[Log condensed; complete log is pinned on host.]\n'+raw[:2000]+'\n[... omitted compiler/unknown-external detail ...]\n'+raw[-12000:]
  r[key]=raw
 elif p.suffix in ['.llbc','.lean']:
  entry=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
  if p.suffix=='.lean':entry['unaccepted_external_declarations']=[{'line':i+1,'text':l} for i,l in enumerate(p.read_text().splitlines()) if re.match(r'^(axiom|opaque) ',l)]
  if p.suffix=='.llbc':
   try:entry['has_errors']=json.loads(p.read_text()).get('has_errors')
   except Exception:pass
  r[str(p.relative_to(E))]=entry
print(json.dumps(r))
'''
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
# Keep full logs/receipts together; source and tool hashes are in their pins.
(DEST/'host-receipts.json').write_text(json.dumps(r,indent=2)+'\n')
print('collected',len(r),'host artifacts as text/hash metadata')
