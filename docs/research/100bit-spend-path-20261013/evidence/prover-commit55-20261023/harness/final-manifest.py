from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
paths=sorted(list((L/'R1Z').glob('ProverCommit*55.lean'))+list((L/'AspisR1ProducerRelease47').glob('*55.lean')))
paths=[p for p in paths if p.stem!='ProverCommitAudit55']
records=[json.loads(p.read_text()) for p in (E/'lean').glob('J*.json')]
roots=[];theorems=[]
for p in paths:
 name=str(p.relative_to(L).with_suffix('')).replace('/','.');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 success=[r for r in records if r.get('module')==name and r.get('source_sha256')==sha and r.get('exit')==0]
 assert success,('no successful current source',str(p))
 roots.append(dict(module=name,path=str(p),sha256=sha,accepted_attempt=success[-1]['attempt']))
 for thm in re.findall(r'^theorem\s+(\S+)',p.read_text(),re.M):
  assert '#print axioms '+thm in p.read_text(),(name,thm)
  theorems.append(name+'.'+thm)
text=''.join('import '+r['module']+'\n' for r in roots)+'import R1Z.ProverCommitAudit54\n'
text+='/-! One final import/axioms manifest over current source-pinned cached objects.\nThis is not a clean rebuild or a release claim. -/\n'
text+=''.join('#print axioms '+t+'\n' for t in theorems)
text+='#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed\n'
(L/'R1Z/ProverCommitAudit55.lean').write_text(text)
m=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),roots=roots,theorems=theorems,scope='Current-source cached dependency import/axioms manifest, not a cold/full frozen release replay')
(E/'final-manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(len(roots),len(theorems))
