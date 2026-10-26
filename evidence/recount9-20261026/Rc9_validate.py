"""Validate prefix sources, receipts, shared-file append integrity and final budget."""
from pathlib import Path
import hashlib,json,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
final='--final' in sys.argv
attempts=[]
for p in sorted(E.glob('Rc9_*/receipt.json')):
 d=json.loads(p.read_text());n=int(d['attempt'].split('_')[1]);assert 1<=n<=60
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in d['command'] and d['swaps']=='0'
 for name,h in d['source_hashes'].items():
  assert name.startswith('Rc9_')
  assert hashlib.sha256((p.parent/'sources'/name).read_bytes()).hexdigest()==h
 if d['exit_status']==0:
  for name,h in d['source_hashes'].items():
   assert hashlib.sha256((R/'lean'/name).read_bytes()).hexdigest()==h,('Delivered source differs',name)
  for line in d['print_axioms']:
   m=re.search(r'axioms: \[(.*)\]',line)
   if m:assert set(m[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'},line
 else:assert n==2,'Unreviewed failed attempt'
 attempts.append({k:d[k] for k in ['attempt','sources','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})
assert len({a['attempt'] for a in attempts})==len(attempts)
if final:
 assert len(attempts)==60
 checked={name for a in attempts if a['exit_status']==0 for name in a['source_hashes']}
 assert checked=={p.name for p in (R/'lean').glob('Rc9_*.lean')},'Unchecked new module'
 axioms=(E/'Rc9_060/stdout.log').read_text()
 for name in ['Rc9_Top.deployed','Rc9_Install.compatible','Rc9_Install.finish_preserved','Rc9_Install.owners','Rc9_Baseline.deployed','Rc9_Transport.rc8_conclusion','Rc9_Reverse.same_witnesses','Rc9_Nonvacuity.composed','Rc9_Clean.exists_world']:
  assert "'AspisR1."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in axioms,name
(E/'Rc9_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in attempts))
for p in (R/'lean').glob('Rc9_*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()),p
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text()),p
pins=json.loads((E/'Rc9_input-pins.json').read_text())
for path in ['design/PREMISE-LEDGER-20261025.md','design/S1-S10-CLOSURE-MAP-20261026.md']:
 data=(R/path).read_bytes();pin=pins[path]
 assert hashlib.sha256(data[:pin['size']]).hexdigest()==pin['sha256'],path
 if final:assert len(data)>pin['size'],path
for p in E.rglob('*'):
 assert p.suffix not in ['.olean','.elf','.tar','.gz'],p
retries={p.name:json.loads(p.read_text()) for p in E.glob('Rc9_*-retries.json') if json.loads(p.read_text())}
summary=dict(admission_retries=retries,lean_attempts=len(attempts),kani_runs=0,passed=sum(a['exit_status']==0 for a in attempts),failed=[a['attempt'] for a in attempts if a['exit_status']],total_lean_wall_seconds=sum(a['wall_seconds'] for a in attempts),maximum_reported_peak_rss_kib=max(int(a['peak_rss_kib']) for a in attempts),swaps=0,final=final,all_existing_shared_sections_intact=True,source_axioms='Only standard axioms on successful targets; Rc9_002 failed diagnostic is excluded')
(E/'Rc9_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
