from pathlib import Path
import hashlib,json,struct,sys,os

def imports(path):
 b=path.read_bytes(); assert b[:5]==b'olean',str(path)
 base,root=struct.unpack_from('<QQ',b,80)
 def u(o): return struct.unpack_from('<Q',b,o)[0]
 def name(p):
  if p&1: assert p==1; return ''
  o=p-base; tag=b[o+7]; prefix=name(u(o+8)); assert tag in [1,2]
  if tag==1:
   q=u(o+16)-base; t=b[q+32:b.index(0,q+32)].decode()
  else: t=str(u(o+16))
  return prefix+'.'+t if prefix else t
 arr=u(root-base+8)-base
 return list(dict.fromkeys(name(u(u(arr+24+8*i)-base+8)) for i in range(u(arr+8))))


B=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
manifest=json.loads((E/'accepted-targets.json').read_text())
focus=set(sys.argv[1:])
if focus:
 assert focus<=manifest['targets'].keys(),focus-manifest['targets'].keys()
 manifest['targets']={n:r for n,r in manifest['targets'].items() if n in focus}
receipts=[json.loads((E/row['receipt']).read_text()) for row in manifest['targets'].values()]
accepted={}
for r in receipts:
 if r['exit_status']==0:
  source=B/'lean-candidates/s126-caller-boundary-20261021'/(r['target']+'.lean')
  if hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']:
   obj=Path('/tmp/s126-current-caller-20261021-objects')/(r['target']+'.olean')
   if obj.exists() and hashlib.sha256(obj.read_bytes()).hexdigest()==r.get('object_sha256'):
    accepted[r['target']]=r
assert accepted,'no accepted current objects'
roots=[Path(x) for x in next(iter(accepted.values()))['lean_path'].split(':')]
# Resolve each target with its own recorded root order, and hash selected closure.
all_modules={}
for target,r in accepted.items():
 roots=[Path(x) for x in r['lean_path'].split(':')];todo=[target];seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);rel=Path(*n.split('.')).with_suffix('.olean')
  path=next((x/rel for x in roots if (x/rel).is_file()),None)
  assert path is not None,(target,n)
  key=str(path)
  if key not in all_modules:
   all_modules[key]=dict(name=n,path=key,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),imports=imports(path))
  todo+=all_modules[key]['imports']
 r['transitive_modules']=sorted(seen)
out=dict(schema='focused-extractor-proof-packet-v1',note='Object hashes only; compiled objects are not distributed. Focused cached compilation, not coherent release rebuild.',targets={n:dict(source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],modules=r['transitive_modules']) for n,r in accepted.items()},modules=list(all_modules.values()))
(E/('focused-import-pins.json' if focus else 'selected-import-pins.json')).write_text('{\n'+',\n'.join(json.dumps(k)+': '+ ('[\n'+',\n'.join(json.dumps(row,separators=(",",":")) for row in v)+'\n]' if k=='modules' else json.dumps(v,separators=(",",":"))) for k,v in out.items())+'\n}\n')
print(json.dumps(dict(targets=len(accepted),objects=len(all_modules))))
