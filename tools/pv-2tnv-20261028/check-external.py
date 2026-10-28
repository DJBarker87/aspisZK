from pathlib import Path
import json,hashlib,sys
B=Path(__file__).resolve().parent
rows=json.load(open(B/'external-authority.json'));out=[]
for r in rows:
 candidate=Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin16-lean/std-cache')/(r['module']+'.olean')
 p=candidate if candidate.is_file() else Path(r['path']);h=hashlib.file_digest(p.open('rb'),'sha256').hexdigest() if p.is_file() else None
 out.append(dict(module=r['module'],path=str(p),sha256=h,expected=r['object_sha256'],match=h==r['object_sha256']))
(B/'external-check.json').write_text(json.dumps(out,indent=2)+'\n')
bad=[r for r in out if not r['match']];print('verified',len(out),'bad',len(bad));print(json.dumps(bad[:15]));sys.exit(bool(bad))
