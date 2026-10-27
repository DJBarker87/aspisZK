"""Restore missing private links for source-resolved EJR imports only.
No h5 object is imported from another job, and shared trees remain read-only.
"""
import pathlib,json,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume6';host='dombarker@100.108.41.90'
rows=[r for r in json.loads((E/'project-closure.json').read_text()) if r['authority']=='EJR']
script='''import pathlib,json,sys,hashlib
rows=json.load(sys.stdin);root=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/objects');env=json.load(open('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/J.json'));roots=[pathlib.Path(x) for x in env['LEAN_PATH'].split(':')];shared=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources');out=[];bad=[]
for r in rows:
 rel=pathlib.Path(*r['module'].split('.'));dst=root/rel.with_suffix('.olean')
 if dst.exists():continue
 source=shared/rel.with_suffix('.lean');sha=hashlib.sha256(source.read_bytes()).hexdigest() if source.is_file() else None
 if sha!=r['sha256']:
  bad.append(dict(module=r['module'],source=str(source),expected=r['sha256'],actual=sha));continue
 src=next((p/rel.with_suffix('.olean') for p in roots if (p/rel.with_suffix('.olean')).is_file()),None)
 if not src:bad.append(dict(module=r['module'],reason='missing object'));continue
 dst.parent.mkdir(parents=True,exist_ok=True);links=[]
 for q in src.parent.glob(src.stem+'.*'):
  p=dst.parent/q.name
  if q.is_file() and not p.exists():
   if p.is_symlink():p.unlink()
   p.symlink_to(q);links.append(dict(path=str(p),target=str(q)))
 out.append(dict(module=r['module'],source=str(source),source_sha256=sha,object=str(src),object_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),links=links))
print(json.dumps(dict(restored=out,held=bad,shared_sources_written=False,h5_objects_linked=False),indent=2))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(script)],input=json.dumps(rows),capture_output=True,text=True,check=True);(E/'pinned-cache-links.json').write_text(r.stdout);d=json.loads(r.stdout);print('restored',len(d['restored']),'held',len(d['held']))
