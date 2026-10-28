from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb2c-20261028'
# Include only exact-source successful modules, plus the final adapters when
# scheduled. Never turn a failed elaboration into an admitted audit premise.
modules=[];source_paths={}
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j['exit']==0 and j.get('module') and int(j['attempt'])<60597:
  module=j['module'];src=R/j['source_path']
  if __import__('hashlib').sha256(src.read_bytes()).hexdigest()==j['source_sha256']:modules.append(module);source_paths[module]=src
modules=sorted(set(modules));names=[]
def uncomment(s):
 out=[];i=0;d=0
 while i<len(s):
  if s[i:i+2]=='/-':d+=1;i+=2
  elif d and s[i:i+2]=='-/':d-=1;i+=2
  elif d:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   k=s.find('\n',i);i=len(s) if k<0 else k
  else:out.append(s[i]);i+=1
 return ''.join(out)
for module in modules:
 s=uncomment(source_paths[module].read_text());stack=[]
 for line in s.splitlines():
  line=line.strip()
  m=re.match(r'namespace\s+(\S+)',line)
  if m:stack.append(m[1]);continue
  if re.match(r'(?:noncomputable\s+)?section\b',line):stack.append(None);continue
  if re.match(r'end(?:\s|$)',line):
   if stack:stack.pop()
   continue
  m=re.match(r'(?:@\[[^]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+(\S+)',line)
  if m:
   name='.'.join([x for x in stack if x]+[m[1]])
   names.append(name)
imports=''.join('import '+m.replace('/','.')+'\n' for m in modules)
(P/'PV_RDB2C_AxiomsAudit.lean').write_text(imports+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(set(names))))
(E/'audit-declarations.json').write_text(json.dumps(dict(modules=modules,theorems=sorted(set(names)),method='all named theorem/lemma commands in exact-source successful owned modules; closure axioms also printed for final row laws'),indent=2)+'\n')
print('audits',len(modules),'modules;',len(set(names)),'theorems')
