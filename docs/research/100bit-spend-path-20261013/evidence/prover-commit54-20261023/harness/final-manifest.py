from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
m=json.loads((E/'final-manifest.json').read_text())
m['modules']=sorted(set(m['modules'])|{'AspisR1ProducerRelease47.EncoderQuery54','R1Z.ProverCommitLeafQuery54'})
m['theorems']=sorted(set(m['theorems'])|{'R1Z.ProverCommitLeafQuery54.folded','R1Z.ProverCommitLeafQuery54.opened'})
m['roots']=[dict(path=str(L/(name.replace('.','/')+'.lean')),sha256=hashlib.sha256((L/(name.replace('.','/')+'.lean')).read_bytes()).hexdigest()) for name in m['modules']]
assert len(m['modules'])==46 and len(m['theorems'])==99
p=L/'R1Z/ProverCommitAudit54.lean'
s=''.join('import '+name+'\n' for name in m['modules'])+'import R1Z.ProverCommitAudit53\n'
s+='/-! Coherent final source audit; every new theorem and the unchanged deployed headline. -/\n'
s+=''.join('#print axioms '+name+'\n' for name in m['theorems'])
s+='#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed\n'
p.write_text(s)
(E/'final-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
