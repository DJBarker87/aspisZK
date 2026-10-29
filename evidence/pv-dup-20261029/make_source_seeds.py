"""Compile source associations from recorded authorities, never grep-selected variants."""
from pathlib import Path
import json,subprocess
B=Path(__file__).resolve().parent
get=lambda f:json.loads(subprocess.check_output(['git','show','4318dfa797:'+f]))
seeds={}
ejr='evidence/envj-rebuild-20261026/EJR_final-inventory.json'
for x in get(ejr)['selected']:
 if x.get('resolution'):seeds[x['module'].replace('/','.')]=dict(source=x['resolution']['path'],sha256=x['sha256'],revision=x['resolution']['revision'],basis=ejr)
f='evidence/replay-dry6-20261026/RPz5_source-plan.json'
for m,x in get(f)['modules'].items():
 if x.get('kind')=='repository':seeds[m]=dict(source=x['source'],sha256=x['sha256'],basis=f)
for f in ['evidence/replay-dry8-20261026/RPz7_source-pins.json','evidence/replay-dry9-20261027/RPz8_source-pins.json']:
 try:d=get(f)
 except subprocess.CalledProcessError:continue
 for x in d['rows']:seeds[x['module']]=dict(source=x['source'],sha256=x['source_sha256'],basis=f)
# RPz8 plan has the same explicit source associations where no separate pins file exists.
f='evidence/replay-dry9-20261027/RPz8_plan.json';d=get(f)
for x in d['rows']:
 if x.get('source'):seeds[x['module']]=dict(source=x['source'],sha256=x.get('sha256',x.get('source_sha256',x.get('original_sha256'))),basis=f)
f='evidence/pv-evhc-20261029/NDR_FINAL_COHORT_PINS.json'
for x in get(f)['entries']:
 if 'source_sha256' in x:seeds[x['module']]=dict(source='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/'+x['module'].replace('.','/')+'.lean',sha256=x['source_sha256'],basis=f,kind='frozen host task source')
# Read other-branch provenance by immutable git revision only; never its worktree.
research_revision='e45a05e2626fd85f9e14ca4faf2dee378470c765'
for f in ['evidence/replay-tops1-20261027/RPt_plan.json','evidence/replay-tops2-20261027/RPu_plan.json','evidence/replay-tops3-20261027/RPv_plan.json','evidence/replay-deployed2-20261027/RPx_plan.json']:
 d=json.loads(subprocess.check_output(['git','show',research_revision+':'+f]))
 for x in d['rows']:
  seeds[x['module']]=dict(source=x['source'],sha256=x.get('sha256'),revision=research_revision,basis=f)
p=json.load(open('/tmp/pv-dup-plan.json'))
for m,x in p['sources'].items():seeds[m]=dict(source=x['path'],sha256=x['sha256'],revision=x['revision'],host_source='/home/dombarker/project-offloads/codex-pv-evhc2-20261029/sources/'+m.replace('.','/')+'.lean',basis='READY reconciled plan.json.sources')
(B/'source-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
mods=set(m for x in json.load(open(B/'collisions.json')) for m in x['modules'])
missing=sorted(m for m in mods if m not in seeds)
(B/'source-seed-missing.json').write_text(json.dumps(missing,indent=2)+'\n')
print('providers',len(mods),'seeded',len(mods)-len(missing),'unseeded',len(missing));print(missing[:70])
