from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=H/'lean/PV_B3Q_MatrixFixture.lean'
rows=[]
for p in H.glob('lean-*/receipt/receipt.json'):
 r=json.loads(p.read_text())
 if r.get('module')=='PV_B3Q_MatrixFixture' and r['exit_status']==0 and r['source_sha256']==sha(source):rows.append((p,r))
assert len(rows)==1
p,r=rows[0];model={}
for line in (p.parent/'stdout.log').read_text().splitlines():
 if line.startswith('"prepared_matrix:'):
  s=json.loads(line);seed,values=s.split(':',1)[1].split('=',1);model[int(seed)]=json.loads(values)
receipt=H/'native-matrix-linear/receipt/receipt.json';native_r=json.loads(receipt.read_text());assert native_r['exit_status']==0
native={}
for line in (receipt.parent/'stdout.log').read_text().splitlines():
 if line.startswith('{'):
  row=json.loads(line);native[row['seed']]=row['limbs']
assert set(native)==set(model)=={0,1,7,19},(native,model)
for seed in model:
 assert len(model[seed])==len(native[seed])==9
 assert native[seed]==model[seed],seed
out=dict(status='pass',matrices=4,entries=36,all_nine_entries=True,model_attempt=r['attempt'],model_source_sha256=sha(source),model_stdout_sha256=sha(p.parent/'stdout.log'),native_receipt_sha256=sha(receipt),native_stdout_sha256=sha(receipt.parent/'stdout.log'),values=model,evidence_class='finite direct comparison of deployed-source private prepared intermediate matrix to emitted model; not universal native caller association',storage_laws=['PV_B3Q_Matrix.deployed_store_link','PV_B3Q_Matrix.entries_injective','PV_B3Q_Matrix.prefix_observations'],compiler_boundary='V370 / D381,D386 retained')
(H/'matrix-emission-comparison.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
