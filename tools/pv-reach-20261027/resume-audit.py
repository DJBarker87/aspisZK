"""Audit every retained declaration added by this resume, then the headline."""
from pathlib import Path
import json,re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-reach-20261027/resume'
core=['CapValue','RetryStep','RetryCongruence','Increment0','Increments','FiniteRetry','ClientFinite','ContinuationRetry','RetryOutcomes','ShapeControl']
groups=[['PV_RE_'+n for n in core]+[f'PV_RE_Continue{i:03}' for i in range(37)],[f'PV_RE_Continue{i:03}' for i in range(37,74) if i not in {63,64}]]
allnames=[];manifest=[]
for tag,modules in zip(['A','B'],groups):
 names=[]
 for m in modules:
  source=(L/(m+'.lean')).read_text()
  names+=['R1Z.'+m+'.'+n for n in re.findall(r'^(?:theorem|def)\s+(\w+)',source,re.M)]
 allnames+=names
 text='\n'.join('import R1Z.'+m for m in modules)+'\n\n'+''.join('#print axioms '+n+'\n' for n in names)
 target=L/f'PV_RE_ResumeAudit{tag}.lean'
 if '--check' in sys.argv:assert target.read_text()==text
 else:target.write_text(text)
 manifest.append(dict(module='R1Z/PV_RE_ResumeAudit'+tag,imports=modules,declarations=names))
text='import R1Z.PV_RE_ResumeAuditA\nimport R1Z.PV_RE_ResumeAuditB\nimport R1Z.PrivacyR1HeadlineDeployedReal\n\n'
text+=''.join('#print axioms '+n+'\n' for n in allnames)
text+='#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed\n'
for n in ['PV_RE_ContinuationRetry.whole_client','PV_RE_ShapeControl.transfer','PV_RE_ShapeControl.withdrawal','PV_RE_RetryCongruence.congr_at']:
 text+='#check @R1Z.'+n+'\n'
target=L/'PV_RE_ResumeCombinedAudit.lean'
if '--check' in sys.argv:assert target.read_text()==text
else:target.write_text(text)
x=dict(groups=manifest,declarations=len(allnames),headline_included=True,kind='focused closure/axioms audit against retained env-J objects; not a clean release replay')
if '--check' in sys.argv:assert json.loads((E/'audit-manifest.json').read_text())==x
else:(E/'audit-manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print('Declarations in resumed audit:',len(allnames))
