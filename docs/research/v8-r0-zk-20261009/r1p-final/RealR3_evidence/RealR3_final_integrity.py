from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[4]
attempts=[json.loads(s) for s in (E/'RealR3_attempts.jsonl').read_text().splitlines()]
assert [r['attempt'] for r in attempts]==list(range(11100,11108))
allowed={'propext','Classical.choice','Quot.sound'}
for r in attempts:
 if r['exit']==0:
  assert r['axioms'] and not r['errors']
  for line in r['axioms']:
   if 'does not depend' not in line:
    names=set(re.search(r'\[([^]]*)\]',line)[1].split(', '));assert names<=allowed,(r['attempt'],line)
final={}
for a,mod in [(11106,'RealR3_SemanticEmission'),(11107,'RealR3_EmissionPrefix')]:
 p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(mod+'.lean');snap=E/'lean-snapshots'/(str(a)+'.lean.txt')
 assert p.read_bytes()==snap.read_bytes()
 row=next(r for r in attempts if r['attempt']==a)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256']==row['snapshot_sha256']
 assert len(re.findall(r'^theorem ',p.read_text(),re.M))==len(row['axioms'])
 final[mod]={'attempt':a,'source_sha256':row['source_sha256'],'axioms':row['axioms']}
native=[json.loads(s) for s in (E/'RealR3_native-attempts.jsonl').read_text().splitlines()];assert len(native)==9
assert sum(r['verified'] for r in native)==4
latest=next(r for r in native if r['name']=='scalar-reachable-zc-first-v9')
for f,h in latest['input_hashes'].items():assert hashlib.sha256((E/'RealR3_native'/f).read_bytes()).hexdigest()==h
assert 'timed out' in (E/'receipts/scalar-reachable-zc-first-v9/stdout.log').read_text()
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.elf','.llbc','.tar','.gz','.pyc','.o'},p
changed=subprocess.check_output(['git','diff','--name-only','1bffe648cad26e07572e4e2e7ac2d4b33795a7de'],cwd=R,text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in changed)
(E/'RealR3_final-integrity.json').write_text(json.dumps({'lean':final,'lean_attempts':len(attempts),'kani_invocations':len(native),'accepted_native_checks':4,'stopping_gate':latest['name'],'stopping_gate_exit':latest['exit_status'],'whole_component_or_endpoint_closed':False,'new_trust_fields':[],'shipped_file_changes':[]},indent=2)+'\n')
print('Final source/receipt integrity passed; no whole-component closure claimed.')
