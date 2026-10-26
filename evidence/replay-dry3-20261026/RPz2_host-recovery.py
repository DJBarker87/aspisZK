"""Read-only recovery from retained historical source/object pairs; no compilation."""
from pathlib import Path
import json,hashlib,sys,re
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=Path('/home/dombarker/project-offloads');g=json.load(sys.stdin);old=g['historical'];plan=g['plan'];found={};missing=[]
roots=[(b/'aspis-joint-20261019/sources-S',b/'aspis-joint-20261019/objects-S'),(b/'aspis-joint-20261019/sources',b/'aspis-joint-20261019/objects')]
def visit(m):
 if m in found:return
 x=plan['modules'].get(m,{})
 if x.get('kind') in ['repository','trusted-library']:return
 suffix=m.replace('.','/');expected=old.get(m,{}).get('object_sha256');selected=None
 for src,obj in roots:
  p=src/(suffix+'.lean');o=obj/(suffix+'.olean')
  if p.is_file() and expected and o.is_file() and h(o)==expected:selected=(p,o);break
 if not selected:missing.append(m);return
 p,o=selected;t=p.read_text();t=re.sub(r'/\-.*?\-/|--[^\n]*',' ',t,flags=re.S);imports=['Init']
 for line in t.splitlines():
  hit=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',line)
  if hit:imports.extend(n for n in re.findall(r'[A-Za-z_][\w.]*',hit[1]) if n!='all')
 imports=list(dict.fromkeys(imports))
 found[m]={'kind':'repository','host_source':str(p),'host_associated_object':str(o),'associated_object_sha256':h(o),'sha256':h(p),'bytes':p.stat().st_size,'imports':imports,'text':p.read_text(),'qualification':'Retained source alongside hash-matched historical selected object; fresh replay required; no claim of an independently retained original source receipt.'}
 for n in imports:visit(n)
plan['modules']['R1NaturalProjection']={'kind':'unresolved'}
for m in plan['unresolved']+['R1NaturalProjection']:visit(m)
print(json.dumps({'recovered':found,'missing':sorted(set(missing))},indent=2))
