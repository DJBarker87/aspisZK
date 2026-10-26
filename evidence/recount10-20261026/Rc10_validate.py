"""Task evidence checks; no compiler or cache mutation."""
from pathlib import Path
import hashlib,json,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1];final='--final' in sys.argv
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
attempts=[]
for p in sorted(E.glob('Rc10_*/receipt.json')):
 d=json.loads(p.read_text());n=int(d['attempt'].split('_')[1]);assert 1<=n<=60
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in d['command'] and d['swaps']=='0'
 for name,h in d['source_hashes'].items():
  assert name.startswith('Rc10_') and sha(p.parent/'sources'/name)==h
 if d['exit_status']==0:
  for name,h in d['source_hashes'].items():assert sha(R/'lean'/name)==h,('Delivered source differs',name)
  for line in d['print_axioms']:
   m=re.search(r'axioms: \[(.*)\]',line)
   if m:assert set(m[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'},line
 else:assert n in [2,6],('Unreviewed failure',n)
 attempts.append({k:d[k] for k in ['attempt','sources','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})
assert len({a['attempt'] for a in attempts})==len(attempts)
(E/'Rc10_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in attempts))
for p in (R/'lean').glob('Rc10_*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()),p
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text()),p
pins=json.loads((E/'Rc10_input-pins.json').read_text())
for path,pin in pins['append_only'].items():
 data=(R/path).read_bytes()
 assert hashlib.sha256(data[:pin['bytes']]).hexdigest()==pin['sha256'],path
 if final:assert len(data)>pin['bytes'],path
if final:
 assert len(attempts)==60
 checked={name for a in attempts if a['exit_status']==0 for name in a['source_hashes']}
 assert checked=={p.name for p in (R/'lean').glob('Rc10_*.lean')},'Unchecked new module'
 axioms=(E/'Rc10_060/stdout.log').read_text()
 for name in ['Rc10_Top.deployed','Rc10_Install.compatible','Rc10_Install.finish_preserved','Rc10_Install.owners','Rc10_Literal.forget','Rc10_Cont.forget','Rc10_Caller.forget','Rc10_Result.forget','Rc10_Reverse.transport','Rc10_Nonvacuity.composed','Rc10_Clean.exists_world']:
  assert "'AspisR1."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in axioms,name
 top=json.loads((E/'Rc10_premises.json').read_text())
 assert len(top['removed'])==7 and top['distinct_delta']['P']==-6 and not top['added']
for p in E.rglob('*'):assert p.suffix not in ['.olean','.elf','.tar','.gz'],p
summary=dict(lean_attempts=len(attempts),kani_runs=0,passed=sum(a['exit_status']==0 for a in attempts),failed=[a['attempt'] for a in attempts if a['exit_status']],total_lean_wall_seconds=sum(a['wall_seconds'] for a in attempts),maximum_reported_peak_rss_kib=max(int(a['peak_rss_kib']) for a in attempts),swaps=0,final=final,all_existing_shared_sections_intact=True,source_axioms='Only standard axioms on successful targets; failed diagnostics 002 and 006 excluded',admission_retries={p.name:json.loads(p.read_text()) for p in E.glob('Rc10_*-retries.json') if json.loads(p.read_text())})
(E/'Rc10_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
