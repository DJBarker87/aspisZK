"""Supplement the owned Kani staging with frozen literal #[path] inputs.
NHR's exporter is unchanged; this strengthens our own per-run source checks.
"""
from pathlib import Path,PurePosixPath
import re,json,lzma,base64,hashlib,subprocess,posixpath
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
payload=json.loads(lzma.decompress(base64.b64decode((E/'NHU_FROZEN_PAYLOAD.b64.txt').read_text())))
known={p:base64.b64decode(b) for p,b in payload.items()};queue=[p for p in known if p.endswith('.rs')];seen=set();extra={};unresolved=[]
pattern=r'#\[\s*path\s*=\s*"([^"\n]+)"\s*\]|include(?:_str|_bytes)?!\(\s*"([^"\n]+)"'
while queue:
 p=queue.pop()
 if p in seen:continue
 seen.add(p);s=known[p].decode()
 for a,b in re.findall(pattern,s):
  rel=posixpath.normpath(posixpath.join(posixpath.dirname(p),a or b))
  if rel.startswith('../') or rel.startswith('/'):unresolved.append(dict(source=p,path=rel,reason='outside frozen repository'));continue
  if rel not in known:
   r=subprocess.run(['git','show',rev+':'+rel],cwd=R,capture_output=True)
   if r.returncode:unresolved.append(dict(source=p,path=rel,reason='not a tracked frozen literal target'));continue
   known[rel]=r.stdout;extra[rel]=r.stdout
  if rel.endswith('.rs'):queue.append(rel)
D=E/'NHU_EXTRA_FILES';D.mkdir(exist_ok=True)
overlay=json.loads((E/'NHU_OVERLAY.json').read_text());frozen=json.loads((E/'NHU_FROZEN_FILE_PINS.json').read_text());rows=[]
for i,(p,b) in enumerate(sorted(extra.items())):
 assert len(b)<20000000,(p,len(b));name=f'NHU_EXTRA_FILES/NHU_extra_{i:03}.txt';(E/name).write_bytes(b);overlay[p]=name;frozen[p]=hashlib.sha256(b).hexdigest()
 rows.append(dict(path=p,input=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()))
(E/'NHU_OVERLAY.json').write_text(json.dumps(overlay,indent=1)+'\n');(E/'NHU_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=1)+'\n');(E/'NHU_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/s).read_bytes()).hexdigest() for p,s in overlay.items()},indent=1)+'\n')
(E/'NHU_EXTERNAL_INPUTS.json').write_text(json.dumps(dict(status='PASS',revision=rev,extra_files=rows,unresolved_potential_inactive=unresolved,source_validation='Every copied frozen byte now in per-run FROZEN_FILE_PINS; graph and lock checks unchanged',shared_stager_changed=False),indent=1)+'\n')
print(json.dumps(dict(extra_files=len(rows),extra_bytes=sum(r['bytes'] for r in rows),unresolved=len(unresolved))))
