from pathlib import Path
import json,sys
p=Path(sys.argv[1]);x=json.loads(p.read_text())['translated']
def walk(t,path=()):
 if isinstance(t,dict):
  for k,v in t.items():
   if k=='Drop':yield path+(k,),v
   yield from walk(v,path+(k,))
 elif isinstance(t,list):
  for i,v in enumerate(t):yield from walk(v,path+(i,))
for f in x['fun_decls']:
 if not f:continue
 found=list(walk(f))
 if found:
  print(json.dumps(dict(id=f['def_id'],name=f['item_meta']['name'],span=f['item_meta'].get('span'),drops=[dict(path=path,place=value.get('place'),kind=value.get('kind'))for path,value in found]),indent=1))
print('function_count',len(x['fun_decls']))
