from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
modules=[];theorems=[]
for p in sorted(E.glob('NBF_*.lean')):
 if p.name=='NBF_Audit.lean':continue
 s=p.read_text();module=p.stem
 accepted=[]
 for r in sorted(E.glob('NBF_L*/receipt.json')):
  x=json.loads(r.read_text())
  if x['exit_status']==0 and any(n.endswith('/'+p.name) for n in x['source_hashes']):accepted.append(x)
 assert accepted,(module,'no accepted source')
 import hashlib
 assert any(hashlib.sha256(p.read_bytes()).hexdigest() in x['source_hashes'].values() for x in accepted),module
 namespace=re.search(r'^namespace (\S+)',s,re.M).group(1)
 names=[namespace+'.'+m.group(1) for m in re.finditer(r'^theorem (\w+)',s,re.M)]
 modules.append(module);theorems+=names
nbb=sorted(p.stem for p in Path('evidence/native-query1-20261027').glob('NBB_*.lean'))
s=''.join('import '+n+'\n' for n in nbb+modules)+'\n'+'\n'.join('#print axioms '+n for n in theorems)+'\n'
(E/'NBF_Audit.lean').write_text(s)
(E/'NBF_THEOREMS.json').write_text(json.dumps(theorems,indent=2)+'\n')
(E/'NBF_MODULES.json').write_text(json.dumps(dict(new_modules=modules,inherited_modules=nbb),indent=2)+'\n')
print(len(modules),'new modules',len(theorems),'public top theorems;',len(nbb),'inherited NBB imports')
