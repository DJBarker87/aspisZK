from pathlib import Path
import subprocess,json,hashlib,re,lzma
E=Path(__file__).resolve().parent
listing=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
paths={}
for p in listing:
 if not p.endswith('.lean'):continue
 name=Path(p).stem
 rank=0 if p.startswith('lean/') and p.count('/')==1 else 1 if p.startswith('docs/research/100bit-spend-path-20261013/lean/') and p.count('/')==5 else 2 if p.startswith('evidence/') and p.count('/')==2 else 9
 if name not in paths or rank<paths[name][0]:paths[name]=(rank,p)
x=json.loads(lzma.decompress(Path('evidence/tx2-model2-20261106/NHT_CLOSURE_PINS.json.xz').read_bytes()));selected={r['module'] for r in x['files']}
graph={};sources={};aliases={};missing=[]
def visit(m):
 if m in graph or m in selected:return
 for prefix in ['NGM_','RPt_','RPz7_','RPx_','NFN_']:
  if prefix+m in selected:
   aliases[m]=prefix+m;return
 if m not in paths and '.' in m:
  rel=m.replace('.','/')+'.lean';hits=[p for p in listing if p.endswith('/'+rel) and '/sources/' not in p and '_extracted/' not in p]
  if hits:paths[m]=(2,sorted(hits,key=len)[0])
 if m not in paths:missing.append(m);return
 p=paths[m][1];s=subprocess.check_output(['git','show','HEAD:'+p],text=True);sources[m]=dict(path=p,source=s,sha256=hashlib.sha256(s.encode()).hexdigest())
 imports=re.findall(r'^import ([\w.]+)',s,re.M);graph[m]=imports
 for n in imports:visit(n)
visit('NET_WideModel')
(E/'NHV_RETARGET_ANALYSIS.json').write_text(json.dumps(dict(aliases=aliases,missing=sorted(set(missing)),graph=graph,sources=sources),indent=2)+'\n')
print(json.dumps(dict(modules=len(graph),aliases=aliases,missing=sorted(set(missing)),modules_list=list(graph)),indent=2))
