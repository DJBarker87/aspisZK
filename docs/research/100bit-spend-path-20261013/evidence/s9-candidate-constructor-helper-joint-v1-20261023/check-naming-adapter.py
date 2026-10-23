from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parent
p=json.loads((r/'source-origin/adapter-pins.json').read_text())
raw=(r/'source-origin/Types.original.lean').read_text()
s=(r/'sources/AspisR1S9ActualWeightsNewBoxNewV1/Types.lean').read_text()
assert hashlib.sha256(raw.encode()).hexdigest()==p['original_sha256']
assert hashlib.sha256(s.encode()).hexdigest()==p['adapted_sha256']
for before,after in reversed(p['blocks']):
 assert s.count(after)==1;s=s.replace(after,before,1)
assert s==raw
m=json.loads((r/'manifest.json').read_text())
for x in m['coherent_dependency_checks']:
 t=json.loads((r/x['receipt']).read_text());assert t['exit_status']==0 and t['process_swaps']==0
assert hashlib.sha256((r/'sources/AspisR1S9ActualWeightsNewBoxNewV1/Funs.lean').read_bytes()).hexdigest()=='97f5a1b269f6d27a6c67fed19f7155d40d7ed19841c60d1fa58a68e038efa2ab'
print('PASS: reversible instance-name expansion, unchanged functions, coherent focused dependency checks')
