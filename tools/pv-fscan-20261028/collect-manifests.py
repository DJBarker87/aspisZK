import pathlib,json,hashlib
D=pathlib.Path('/home/dombarker/project-offloads');names=['pv-cb-20261026','pv-cb3-20261026','pv-cb9-20261027','pv-cbmid-20261027','pv-cblib-20261027','pv-alib-20261027','pv-batch1-20261027','pv-batch2-20261027','pv-batch3-20261027','pv-op223-20261027','pv-dlib-20261028','pv-b3p6-20261028','pv-fxmem-20261028','pv-relink-20261028','pv-kstub-20261028'];out=[]
for n in names:
 d=D/('codex-'+n)
 for pattern in ['*/Cargo.toml','*/*/Cargo.toml','Cargo.toml']:
  for p in d.glob(pattern):
   if any(x in p.parts for x in ['target','src','source','original','candidate','applied']):continue
   b=p.read_bytes();out.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(out,indent=2))
