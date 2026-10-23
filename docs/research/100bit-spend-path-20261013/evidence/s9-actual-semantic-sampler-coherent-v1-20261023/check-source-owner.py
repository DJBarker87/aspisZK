from pathlib import Path
import json,hashlib
r=Path(__file__).resolve().parent
p=json.loads((r/'source-origin/adapter-pins.json').read_text())
raw=(r/'source-origin/Types.normalized-original.lean').read_text()
s=(r/'sources/AspisR1ActualSemanticRoundCutV1/Types.lean').read_text()
assert hashlib.sha256(raw.encode()).hexdigest()==p['original_sha256']
assert hashlib.sha256(s.encode()).hexdigest()==p['adapted_sha256']
for before,after in reversed(p['blocks']):
 assert s.count(after)==1;s=s.replace(after,before,1)
assert s==raw
f=(r/'source-origin/Funs.raw-generated.lean').read_text()
a=f.index('/-- [aspis_r1_cost_probe::sampler::qm31_div_pass]: loop body 0:')
b=f.index('/-- [aspis_r1_cost_probe::r1_semantic::semantic_round]:',a)
selected=f[a:b].strip()
assert selected.count('32#i32')==1
selected=selected.replace('32#i32','32#u32')
s=(r/'sources/AspisR1ActualSemanticRoundCutV1/Funs.lean').read_text()
a=s.index('/-- [aspis_r1_cost_probe::sampler::qm31_div_pass]: loop body 0:')
b=s.rindex('end AspisR1ActualSemanticRoundCutV1')
assert [x for x in s[a:b].splitlines() if x.strip()]==[x for x in selected.splitlines() if x.strip()]
m=json.loads((r/'manifest.json').read_text())
for x in m['coherent_dependency_checks']:
 t=json.loads((r/x['receipt']).read_text());assert t['exit_status']==0 and t['process_swaps']==0
 log=(r/x['receipt']).with_name('lean.log').read_text();assert 'sorryAx' not in log and 'error:' not in log
print('PASS: reversible names-only adapter, exact selected generated sampler span with one typed shift-count port, coherent focused dependency checks')
