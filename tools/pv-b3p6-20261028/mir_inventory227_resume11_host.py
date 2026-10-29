"""Read-only deployed MIR/symbol inventory, retaining inline evidence per body."""
from run import H
from pathlib import Path
import json,re,hashlib,subprocess,lzma
inv=json.loads((H/'body-inventory-resume11.json').read_text());allmir=[];inputs=[];symbols=[]
for package in ['aspis-r1-cost-probe','aspis-statement','aspis-core']:
 a=json.loads((H/('mir227-resume11-'+package+'.json')).read_text())
 for r in a['artifacts']:
  p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
  inputs.append(r)
  if p.suffix=='.mir':
   selected=[];owner=''
   for line,l in enumerate(p.read_text().splitlines(),1):
    if l.startswith('fn '):owner=l
    if l.startswith('fn ')or'(inlined 'in l or re.search(r'= .*\w+\(',l):selected.append((line,l,owner))
   allmir.append((str(p),selected))
  elif p.suffix=='.ll':
   for line in p.read_text().splitlines():
    if line.startswith(('define ','declare ','; ')):symbols.append(dict(artifact=str(p),text=line))
rows=[]
for r in inv['bodies']:
 name=r['key'].split('#')[0];pattern=re.compile(r'(?<!\w)'+re.escape(name)+r'(?!\w)');hits=[]
 for path,selected in allmir:
  for line,l,owner in selected:
   if pattern.search(l)and (l.startswith('fn ')or'(inlined 'in l or re.search(r'= .*\b'+re.escape(name)+r'\(',l)):
    hits.append(dict(artifact=path,line=line,enclosing_function=owner,text=l))
 sym=[s for s in symbols if pattern.search(s['text'])or(name!=''and name not in ['new','mul','$']and name in s['text'])]
 rows.append(dict(family=r['family'],key=r['key'],mir_witnesses=hits,llvm_symbol_witnesses=sym,absence_is_not_dead_code_evidence=True))
x=dict(artifacts=inputs,bodies=rows,features='llvm227-features-resume7.json',toolchain='1.94.1',profile='release,opt3,overflow-checks=false,debug-assertions=false',boundary='Supporting source selection and inline occurrence inventory; source graph controls conservative reachability; no source-to-machine preservation theorem.')
(H/'mir-inventory-resume11.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(bodies=len(rows),mir_hits=sum(bool(r['mir_witnesses'])for r in rows),llvm_hits=sum(bool(r['llvm_symbol_witnesses'])for r in rows))))
