from pathlib import Path
import json,re
E=Path(__file__).resolve().parent.parent
S=Path('docs/research/v8-r0-zk-20261009/lean')
mods=sorted((S/'R1Z').glob('ProverCommit*47.lean'))
mods=[p for p in mods if p.name!='ProverCommitAudit47.lean']
names=[]
for p in mods:
 s=p.read_text();ns=re.search(r'^namespace (R1Z\.\w+)',s,re.M)[1]
 names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M))
text='\n'.join('import '+str(p.relative_to(S))[:-5].replace('/','.') for p in mods)
text+='\nimport R1Z.ProverCommitDeployedFuel22\n\n'
text+='\n'.join('#print axioms '+n for n in names)
text+='\n#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed\n'
(S/'R1Z/ProverCommitAudit47.lean').write_text(text)
(E/'theorem-inventory.json').write_text(json.dumps(dict(theorems=names,count=len(names),scope='Audit coverage only; this is not a security-progress metric.'),indent=2)+'\n')
print(len(names))
