"""Keep every continuation attempt, including failed audits and launch refusals."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/stage3'
allowed={'propext','Classical.choice','Quot.sound'}
rows=[]
for p in sorted(E.glob('*-receipt.json')):
 x=json.loads(p.read_text());a=x['attempt']
 log=(E/f'out-{a}.log').read_text() if (E/f'out-{a}.log').exists() else ''
 lines=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 axioms=[]
 for line in lines:
  if 'depends on axioms:' in line:axioms+=line.split('[',1)[1].rstrip(']').replace('\n','').split(',')
 forbidden=sorted({s.strip() for s in axioms}-allowed)
 x.update(print_axioms=lines,forbidden_axioms=forbidden,compiled=x['exit_status'] is not None,accepted=x['exit_status']==0 and not forbidden)
 for key,label in [('wall_time','Elapsed (wall clock) time (h:mm:ss or m:ss)'),('peak_rss_kib','Maximum resident set size (kbytes)'),('swaps','Swaps')]:
  m=re.search(re.escape(label)+r':\s*([^\n]+)',x['time_log']);x[key]=m[1] if m else None
 if a in range(11212,11216):x['source_revision_correction']=dict(recorded=x['source_revision'],actual_base='dc479c23a029d59a767ecd37b32286b9901abdc1',reason='Inherited revision.txt was stale during first four continuation attempts; exact compiled source hashes and snapshots retained')
 rows.append(x)
new=[r for r in rows if r['attempt']>=11212]
result=dict(status='Partial Stage 3; parameterized caller, selected sampler and retry control; native instance and RunJoin remain open',all_lean_compiles=sum(r['compiled'] for r in rows),continuation_lean_compiles=sum(r['compiled'] for r in new),continuation_ids=[r['attempt'] for r in new],lean_budget=100,remaining_lean_compiles=100-sum(r['compiled'] for r in rows),new_kani_runs=0,total_kani_runs=42,kani_budget=60,next_attempt=max(r['attempt'] for r in rows)+1,rows=new,qualified_full_dictionary=dict(types=28,functions=262,concretely_installed_functions=['sampler.qm31_sample'],uninstalled_function_entries=261),whole_attempt_proved=False,conjunct_1_proved=False,adopted=False,source_model_native_equivalence_of_all_emission_normalizations=False)
(E/'continuation-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['rows','qualified_full_dictionary']}))
