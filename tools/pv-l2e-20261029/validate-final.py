"""Summarize immutable receipts; no compiler launch or regression rerun."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path('evidence/pv-l2e-20261029')
rows=sorted([json.load(open(p)) for p in E.glob('receipt-679*.json')],key=lambda r:r['attempt'])
assert [r['attempt'] for r in rows]==list(range(67900,68000)),len(rows)
assert all(r['admission']['allowed'] is True for r in rows)
accepted=[r for r in rows if r['accepted']]
allowed={'propext','Classical.choice','Quot.sound'}
for r in accepted:
 assert r['exit']=='0'
 for line in r['axioms']:
  if 'depends on axioms:' in line:
   terms=set(re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n','').replace(' ','').split(','))
   assert terms<=allowed,(r['attempt'],line)
manifest=json.load(open(E/'final-focused-manifest.json'))
byid={r['attempt']:r for r in rows}
cohort=json.load(open(E/'final-cohort-check.json'))['result']
expected={v['module']:v['sha256'] for v in cohort['objects']}
comparisons=[]
for x in manifest['replay']:
 r=byid[x['attempt']];assert r['accepted'] and r['source_sha256']==x['sha256']
 assert r['object_sha256']==expected[x['module']],('fresh object mismatch',x['module'])
 comparisons.append(dict(attempt=x['attempt'],module=x['module'],source_sha256=x['sha256'],object_sha256=r['object_sha256']))
assert all(byid[a]['accepted'] for a in [67997,67998,67999])
assert not subprocess.check_output(['git','diff','67b128b900','--name-only','--','crates/','programs/'])
assert all(p.stat().st_size<=20*1024**2 for p in E.rglob('*') if p.is_file())
assert not list(E.glob('refusal-*.json'))
failed=[dict(attempt=r['attempt'],target=r['target'],exit=r['exit'],peak_rss_kbytes=r['peak_rss_kbytes'],wall=r['wall']) for r in rows if not r['accepted']]
for i,r in enumerate(rows):
 for p in rows[:i]:
  assert not (p['target']==r['target'] and not p['accepted'] and p['source_sha256']==r['source_sha256']),('unchanged failure rerun',r['attempt'])
checks=dict(lean_attempts=len(rows),focused_attempts=manifest['focused_attempts'],failed_focused_attempts=failed,final_replay_targets=len(manifest['replay']),combined_audits=[67997,67998,67999],accepted_axioms=sorted(allowed),all_accepted_results_have_standard_axioms_only=True,peak_rss_all_kib=max(int(r['peak_rss_kbytes']) for r in rows),peak_rss_accepted_kib=max(int(r['peak_rss_kbytes']) for r in accepted),total_swaps=sum(int(r['swaps']) for r in rows),native_scopes=1,kani_runs=0,wrapper_sha256=hashlib.sha256(Path('tools/pv-l2e-20261029/compile.py').read_bytes()).hexdigest(),preflight_object_checks=len(cohort['objects']),fresh_object_comparisons=comparisons,unchanged_reused_own_objects=manifest['reused_own_objects'],native_result=json.load(open(E/'receipt-sampler-native.json'))['exit'],instantiated_top_theorem=False,first_fifteen_requirement_met=False,whole_links_discharged=[],endpoint_premises_removed=[],stop='100/100 Lean attempts exhausted',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'FINAL-VALIDATION.json').write_text(json.dumps(checks,indent=2)+'\n')
(E/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline','67b128b900..HEAD'],text=True))
print(json.dumps({k:v for k,v in checks.items() if k not in ['fresh_object_comparisons','failed_focused_attempts']},indent=2))
