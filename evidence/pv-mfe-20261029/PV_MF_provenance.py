from pathlib import Path
import json,subprocess,hashlib
D=Path(__file__).resolve().parent
paths=['evidence/pv-rw19-resume-20261026/27828-input.json','evidence/pv-rw19-resume-20261026/retained-source-provenance.json','evidence/pv-rw19-resume-20261026/focused-dependencies.json','docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/effect/11286-input.json','docs/research/100bit-spend-path-20261013/evidence/import-union-20261022/host-module-graph.json']
r={}
for p in paths:
 b=subprocess.check_output(['git','show','HEAD:'+p]);r[p]=dict(sha256=hashlib.sha256(b).hexdigest(),content=json.loads(b))
(D/'provenance-input.json').write_text(json.dumps(r,indent=2)+'\n')
