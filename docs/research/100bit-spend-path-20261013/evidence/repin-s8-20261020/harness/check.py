"""Read-only packet check; does not replay extraction or Lean."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parents[1]
B=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((E/'source-validation.json').read_text())['all_match']
assert len(json.loads((E/'source-validation.json').read_text())['files'])==58
for p in json.loads((E/'inherited-generated-pins.json').read_text()):
 assert sha(E/p['path'])==p['sha256']
raw=(E/'inherited-stage2/Funs.lean').read_text()
s=(B/'lean/S8FrozenRow.lean').read_text()
for row in json.loads((E/'row-body-binding.json').read_text())['declarations']:
 name=row['name']
 a=raw.index('def '+name+'\n');body=raw[a:raw.index('\n/--',a)].strip()
 assert body in s and hashlib.sha256(body.encode()).hexdigest()==row['sha256']
for p in [E/'inherited-stage2/Types.lean',B/'lean/extracted-source-proof-loops-20261019/AspisR1BatchedWeightsExtraction/Types.lean']:
 assert 'def aspis_core.field.M31 := Std.U32' in p.read_text()
assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',s)
accepted=json.loads((E/'manifest.json').read_text())['accepted_proofs']
for name in accepted:
 r=json.loads((E/name).read_text())
 assert r['exit_status']==0 and r['source_sha256']==sha(B/'lean/S8FrozenRow.lean')
 assert r['print_axioms'] and all('sorryAx' not in x for x in r['print_axioms'])
 for x in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^\]]*)\]',x)
  if m:assert set(y.strip() for y in m[1].split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert not list(E.rglob('*.llbc')) and not list(E.rglob('*.olean'))
print('packet pins, exact row body, standard axioms, and artifact exclusions pass')
