"""Lexical inventory of all public PV_Join theorem names and import coverage."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
files=sorted(f for f in p.glob('PV_Join_*.lean') if 'CombinedAudit' not in f.stem)
names=[];sources=[]
for f in files:
 s=f.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)
 ts=re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)',s,re.M)
 if ts:assert ns,f
 names.extend(ns[1]+'.'+t for t in ts)
 sources.append(dict(module='R1Z.'+f.stem,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),theorems=ts))
parts=int(sys.argv[1]) if len(sys.argv)>1 else 0
part_modules=[]
for idx in range(parts):
 group=sources[len(sources)*idx//parts:len(sources)*(idx+1)//parts]
 body=''.join('import '+x['module']+'\n' for x in group)+'\n'
 for x in group:
  for t in x['theorems']:
   body+='#print '+x['module']+'.'+t+'\n#print axioms '+x['module']+'.'+t+'\n'
 part='PV_Join_CombinedAuditPart'+str(idx+1);part_modules.append('R1Z.'+part)
 (p/(part+'.lean')).write_text(body)
text=''.join('import '+m+'\n' for m in part_modules)+'import R1Z.PrivacyR1HeadlineDeployedReal\n'+''.join('import R1Z.'+f.stem+'\n' for f in files)+'\n'
text+='-- All public theorem declarations in the PV_Join modules, including inherited drafts.\n'
text+=''.join('#print axioms '+n+'\n' for n in sorted(set(names)))
text+='#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed\n'
(p/'PV_Join_CombinedAudit.lean').write_text(text)
(r/'evidence/pv-join-20261026/resume3/combined-audit-manifest.json').write_text(json.dumps(dict(sources=sources,theorems=sorted(set(names)),part_modules=part_modules,headline_import=True,kind='source coverage manifest; compilation and axiom validation required'),indent=2)+'\n')
print(len(files),'modules',len(names),'theorems')
