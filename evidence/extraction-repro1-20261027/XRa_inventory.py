import pathlib,os,json,hashlib,subprocess
root=pathlib.Path('/home/dombarker/project-offloads')
names=[p for p in root.iterdir() if any(s in p.name.lower() for s in ['aeneas','charon','r18-tools','tag73','toolchain'])]
print('WORKSPACES',json.dumps([str(p) for p in names]))
for p in names:
 for base,dirs,files in os.walk(p):
  depth=len(pathlib.Path(base).relative_to(p).parts)
  dirs[:]=[d for d in dirs if d not in ['target','.git','_opam','node_modules','.lake'] and (depth<4 or d in ['output','bin'])]
  for f in files:
   q=pathlib.Path(base)/f
   if any(s in f.lower() for s in ['aeneas','charon','patch','pin','manifest','build','archive']) and (depth<3 or 'extended' in f):
    try:
     size=q.stat().st_size
     h=hashlib.file_digest(q.open('rb'),'sha256').hexdigest() if size<40000000 else None
     print(json.dumps({'path':str(q),'bytes':size,'sha256':h}))
    except OSError as e:print(str(e))
for q in [root/'v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static',root/'aspis-r1-r18-tools-20261016/charon-target/release/charon',root/'aspis-r1-r18-tools-20261016/charon-target/release/charon-driver']:
 print('PIN',str(q),'exists',q.exists())
