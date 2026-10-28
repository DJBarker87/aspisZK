from pathlib import Path
import json,subprocess,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d369'
manifest=json.loads((R/'evidence/pv-runjoin20-20261027/external-object-manifest.json').read_text())
code='''import pathlib,json,hashlib,sys
rows=json.load(sys.stdin);out=[]
e=json.load(open('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean/J.json'))
roots=[pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean/objects')]+[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')]
for r in rows:
 rel=r['module'].replace('.','/')+'.olean'
 p=next((root/rel for root in roots if (root/rel).exists() or (root/rel).is_symlink()),pathlib.Path('/NO_SELECTED_OBJECT'))
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 out.append(dict(module=r['module'],path=str(p),sha256=h,expected=r['object_sha256'],match=h==r['object_sha256']))
print(json.dumps(out))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(manifest),text=True,capture_output=True)
assert p.returncode==0,p.stderr
rows=json.loads(p.stdout);(E/'actual-prefix-external-hash-check.json').write_text(json.dumps(rows,indent=2)+'\n')
assert all(r['match'] for r in rows),[r for r in rows if not r['match']]
print('Verified',len(rows),'actual external objects against h4/SCOPE authority; no endpoint compile')
