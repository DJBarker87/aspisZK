from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent.parent
rows=json.loads(Path('/tmp/p25-imports.json').read_text())
L=Path('docs/research/v8-r0-zk-20261009/lean')
for row in rows:
 p=L/(row['module'].replace('.','/')+'.lean');assert not p.exists(),p
 p.parent.mkdir(parents=True,exist_ok=True)
 raw=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+row['source']])
 assert hashlib.sha256(raw).hexdigest()==row['sha256']
 d=E/'extraction/sampler-owners';d.mkdir(parents=True,exist_ok=True)
 (d/(row['module']+'.lean.txt')).write_bytes(raw)
 s=raw.decode();t=s.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n')
 if row['module']=='IndexedCandidateDecode8RetainedBridgeV3':
  t=t.replace('import ExtractedMaskHornerStep','import R1Z.ProverCommitArrayIndex25').replace('AspisR1.ExtractedMaskHornerStep.array_index_usize_ok','R1Z.ProverCommitArrayIndex25.array_index_usize_ok')
 p.write_text(t)
 row['promoted_sha256']=hashlib.sha256(t.encode()).hexdigest()
 (d/(row['module']+'.diff')).write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='retained/'+row['module'],tofile='env-J/'+row['module'])))
(E/'sampler-owners.json').write_text(json.dumps(rows,indent=2)+'\n')
p=E/'harness/lean.py';s=p.read_text();s=s.replace("assert rel.startswith(","assert rel in "+repr([r['module'].replace('.','/')+'.lean' for r in rows])+" or rel.startswith(",1)
# Include the full imported owner cone in the evidence fingerprint.
s=s.replace("if q.exists() and m.startswith(","if q.exists() and (m in "+repr([r['module'] for r in rows])+" or m.startswith(").replace("'R1Z.ProverCommit')):","'R1Z.ProverCommit'))):")
p.write_text(s)
