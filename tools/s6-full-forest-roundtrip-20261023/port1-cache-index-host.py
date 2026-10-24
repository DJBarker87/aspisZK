from pathlib import Path
import hashlib,json,struct
r=json.loads(Path('/home/dombarker/project-offloads/codex-cx-ports1-20261023/lean-021.json').read_text());roots=[Path(p) for p in r['env']['LEAN_PATH'].split(':')]
def imports(path):
 b=path.read_bytes();base,root=struct.unpack_from('<QQ',b,80)
 def u(o):return struct.unpack_from('<Q',b,o)[0]
 def name(p):
  if p&1:return ''
  o=p-base;t=b[o+7];prefix=name(u(o+8))
  if t==1:
   q=u(o+16)-base;v=b[q+32:b.index(0,q+32)].decode()
  else:v=str(u(o+16))
  return prefix+'.'+v if prefix else v
 a=u(root-base+8)-base
 return list(dict.fromkeys(name(u(u(a+24+8*i)-base+8)) for i in range(u(a+8))))
todo=['Port1_ByteDriver'];seen={}
while todo:
 n=todo.pop()
 if n in seen:continue
 rel=Path(*n.split('.')).with_suffix('.olean');p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p,n
 seen[n]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=imports(p));todo+=seen[n]['imports']
print(json.dumps(seen))
