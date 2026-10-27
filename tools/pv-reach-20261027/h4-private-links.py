import pathlib,json,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2]; E=R/'evidence/pv-reach-20261027/resume3'
script='''import json,pathlib,sys,hashlib
rows=json.load(sys.stdin);root=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/objects');links=[]
for r in rows:
 p=pathlib.Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256']
 rel=pathlib.Path(r['module']).with_suffix('.olean');dst=root/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 for src in p.parent.glob(p.stem+'.*'):
  if src.is_file():
   q=dst.parent/src.name
   if not q.exists() and not q.is_symlink():q.symlink_to(src);links.append(dict(path=str(q),target=str(src)))
print(json.dumps(dict(links=len(links),shared_sources_written=False,library_object_rebuilt=False,authority='h4',examples=links[:6])))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=(E/'external-object-manifest.json').read_text(),text=True,capture_output=True,check=True)
(E/'cache-links.json').write_text(r.stdout);print(r.stdout)
