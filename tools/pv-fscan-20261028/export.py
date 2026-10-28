import pathlib,tarfile,sys
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028')
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for p in D.glob('*/*'):
  if p.is_file() and p.name in ['features.json','unit-graph.json','metadata.json.xz','metadata.json.sha256','mir-identity.json','command.json','crate.mir.xz']:
   t.add(p,arcname='artifacts/'+str(p.relative_to(D)),recursive=False)
 for name in ['upload-admission.json','upload-admission.log','dump-manifest.json']:
  p=D/name
  if p.exists():t.add(p,arcname=name,recursive=False)
