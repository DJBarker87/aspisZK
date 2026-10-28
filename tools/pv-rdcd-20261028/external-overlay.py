from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');out=[]
for r in json.load(open(D/'external-object-manifest.json')):
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],r['module']
 q=D/'external-objects'/(r['module']+'.olean');q.parent.mkdir(exist_ok=True,parents=True);q.symlink_to(p)
 for suffix in ['.ir','.olean.server','.olean.private']:
  a=p.with_suffix(suffix)
  if a.exists():
   b=q.with_suffix(suffix);b.symlink_to(a);out.append(dict(path=str(b),source=str(a),sha256=hashlib.sha256(a.read_bytes()).hexdigest()))
e=json.load(open(D/'env-J.json'));parts=e['LEAN_PATH'].split(':');e['LEAN_PATH']=':'.join([parts[0],str(D/'external-objects')]+parts[1:]);(D/'env-J.json').write_text(json.dumps(e,indent=2)+'\n')
(D/'external-overlay.json').write_text(json.dumps(dict(companions=out,reason='Private Env-J namespace lookup repair after41402; unchanged pinned objects; no shared writes'),indent=2)+'\n');print('Pinned external overlay ready;',len(out),'companions')
