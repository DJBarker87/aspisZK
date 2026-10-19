#!/usr/bin/env python3
"""Read-only source import inventory; this does not select/rebuild old objects."""
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess
root=Path.cwd(); out=root/'.r18-prefix-check/selected-frontier'
revision='b330ade02e82770977de48471ee0d0b886c0e796'
sha=lambda b:hashlib.sha256(b).hexdigest()
old=json.loads((root/'.semantic-prefix-check/host-bridge/manifest.json').read_text())
paths={n:x['source'] for n,x in old['dependency_pins'].items()}
for name in ['SemanticPrefixAgreement','SemanticPrefixCompletedAgreement','SemanticPrefixCutAgreement']:
 paths['R1'+name]='docs/research/100bit-spend-path-20261013/lean/'+name+'.lean'
external=('Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient')
current={x['module']:x for x in json.loads((root/'.r18-prefix-check/semantic-frontier/current144-audit.json').read_text())['targets']}
coherent=json.loads((root/'.r18-prefix-check/semantic-frontier/full-inventory.json').read_text())['modules']
r17=json.loads((out/'r17-producing-inventory.json').read_text())['modules']
fresh={}
for bundle in ['r18-current-framing-closure-20261016','r18-duplex-symbolic-compat-20261016','r18-prefix-frame-agreement-20261016','r18-prefix-semantic-low-20261016','r18-prefix-typed-semantic-20261016']:
 b=root/'docs/research/100bit-spend-path-20261013/evidence'/bundle
 for p in b.rglob('receipt.json'):
  r=json.loads(p.read_text())
  if r.get('exit_status')==0 and r.get('olean_sha256'):
   fresh[r['target']]={'receipt':str(p.relative_to(root)),'source_sha256':r['source_sha256'],'object_sha256':r['olean_sha256']}
def imports(text):
 # Nested Lean block comments and line comments, preserving newlines. Only
 # inspect the module header, before any declaration/string can occur.
 clean=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;i+=2;continue
  if depth and text.startswith('-/',i):depth-=1;i+=2;continue
  if depth:
   if text[i]=='\n':clean.append('\n')
   i+=1;continue
  if text.startswith('--',i):
   while i<len(text) and text[i]!='\n':i+=1
   continue
  clean.append(text[i]);i+=1
 result=[]
 for line in ''.join(clean).splitlines():
  s=line.strip()
  if not s or s=='prelude':continue
  if s.startswith('public import '):result+=s[14:].split()
  elif s.startswith('import '):result+=s[7:].split()
  else:break
 return result
catalog={};missing=[]
def walk(n):
 if n.startswith(external) or n in catalog:return
 if n not in paths:missing.append(n);return
 data=subprocess.check_output(['git','show',revision+':'+paths[n]],cwd=root)
 h=sha(data);deps=imports(data.decode())
 matches=[]
 for label,bag in [('own-focused',fresh),('coherent46',coherent),('current144',current),('R17-producing',r17)]:
  if n in bag and bag[n]['source_sha256']==h:matches.append(label)
 own=(root/paths[n]).read_bytes()
 catalog[n]={'source':paths[n],'source_sha256':h,'imports':deps,'source_matching_receipt_sets':matches,'own_branch_source_sha256':sha(own),'own_branch_source_matches':own==data}
 for dep in deps:walk(dep)
targets=['R1SemanticPrefixAgreement','R1SemanticPrefixCompletedAgreement','R1SemanticPrefixCutAgreement']
for target in targets:walk(target)
closures={}
for target in targets:
 seen=set()
 def visit(n):
  if n not in catalog or n in seen:return
  seen.add(n)
  for d in catalog[n]['imports']:visit(d)
 visit(target)
 closures[target]={'modules':sorted(seen),'project_module_count':len(seen),'without_source_matching_receipt_in_audited_sets':sorted(n for n in seen if not catalog[n]['source_matching_receipt_sets'])}
report={'source_revision':revision,'own_branch_revision':'72c35a2b3ebfb10b125e1797fc1562bc0ea26efa','scope':'Source-only import frontier. Matching receipt categories are not combined-object coherence and do not prescribe a rebuild. No historical374 object selected. No dependency replay.','catalog':catalog,'closures':closures,'unmapped_project_imports':sorted(set(missing)),'receipt_sets':{'current144_sha256':sha((root/'.r18-prefix-check/semantic-frontier/current144-audit.json').read_bytes()),'coherent46_sha256':sha((root/'.r18-prefix-check/semantic-frontier/full-inventory.json').read_bytes()),'r17_inventory_sha256':sha((out/'r17-producing-inventory.json').read_bytes())},'own_focused_receipts':fresh}
(out/'current-source-frontier.json').write_text(json.dumps(report,indent=2)+'\n')
for n,c in closures.items():print(n,c['project_module_count'],'without matching receipt',len(c['without_source_matching_receipt_in_audited_sets']))
print('unmapped',report['unmapped_project_imports'])
print('source differences from own branch',[n for n,x in catalog.items() if not x['own_branch_source_matches']])
