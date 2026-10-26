from pathlib import Path
import json,hashlib,sys,re
z=json.load(sys.stdin);g=z['plan'];old=z['historical'];located=z['located'];roots=set();h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();found={};seen=set();unresolved=[]
for m,rows in located.items():
 for row in rows:
  if row['associated_object']:
   roots.add((row['path'][:-len(m.replace('.','/')+'.lean')],row['associated_object'][:-len(m.replace('.','/')+'.olean')]))
def visit(m):
 if m in seen:return
 seen.add(m)
 if g['modules'].get(m,{}).get('kind') in ['repository','trusted-library']:return
 if m.split('.')[0] in {'Init','Lean','Std','Lake','Mathlib','Aeneas','AeneasMeta','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Cli'}:return
 candidates=[];expected=old.get(m,{}).get('object_sha256');suffix=m.replace('.','/')
 for src,obj in sorted(roots):
  p=Path(src)/(suffix+'.lean');o=Path(obj)/(suffix+'.olean')
  if p.is_file() and o.is_file() and expected and h(o)==expected:candidates.append((p,o,h(p)))
 if len({x[2] for x in candidates})!=1:unresolved.append({'module':m,'source_variants':len({x[2] for x in candidates})});return
 p,o,sha=candidates[0];text=p.read_text();t=re.sub(r'/\-.*?\-/|--[^\n]*',' ',text,flags=re.S);imports=['Init']
 for line in t.splitlines():
  hit=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)',line)
  if hit:imports.extend(n for n in re.findall(r'[A-Za-z_][\w.]*',hit[1]) if n!='all')
 imports=list(dict.fromkeys(imports));found[m]={'kind':'repository','host_source':str(p),'host_associated_object':str(o),'associated_object_sha256':expected,'sha256':sha,'bytes':p.stat().st_size,'imports':imports,'text':text,'qualification':'Unique source variant across located roots with adjacent hash-matched historical selected objects. Original source receipt not independently established; fresh replay required.'}
 for n in imports:visit(n)
for m in g['unresolved']:visit(m)
print(json.dumps({'recovered':found,'unresolved':unresolved,'roots':sorted(roots)},indent=2))
