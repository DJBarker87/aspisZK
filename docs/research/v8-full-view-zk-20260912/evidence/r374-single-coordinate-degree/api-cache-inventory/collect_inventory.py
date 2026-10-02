#!/usr/bin/env python3
"""Read-only local/host source and Lean-cache census; does not invoke Lean."""
from __future__ import annotations
import hashlib,json,re,subprocess,shlex
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
LEAN=ROOT/'docs/research/v8-full-view-zk-20260912/lean'
START='AspisV8R19.SourceStatementPoints'
PREFIX=('AspisV8','AspisV7','AspisR','AspisFormal')
seen=set(); pending=[START]; imports={}; missing=[]
while pending:
 module=pending.pop()
 if module in seen:continue
 seen.add(module)
 path=LEAN.joinpath(*module.split('.')).with_suffix('.lean')
 if not path.is_file():missing.append(module);continue
 imps=re.findall(r'^import\s+([A-Za-z0-9_.]+)',path.read_text(),re.M)
 imports[module]=imps
 pending.extend(x for x in imps if x.startswith(PREFIX))
external=sorted({x for xs in imports.values() for x in xs if not x.startswith(PREFIX)})
local_rows=[]
for module in sorted(seen):
 p=LEAN.joinpath(*module.split('.')).with_suffix('.lean')
 local_rows.append({'module':module,'path':p.relative_to(ROOT).as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'imports':imports.get(module,[])})
payload={'aspis':sorted(seen),'external':external}
remote_py=r'''import hashlib,json,pathlib,sys
x=json.load(sys.stdin)
src=pathlib.Path('/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a')
cache=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib')
math=pathlib.Path('/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib')
def row(m,root,base):
 p=root.joinpath(*m.split('.')).with_suffix('.lean')
 o=base.joinpath(*m.split('.')).with_suffix('.olean')
 def h(q):return hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None
 return {'module':m,'source_exists':p.is_file(),'source_sha256':h(p),'olean_exists':o.is_file(),'olean_sha256':h(o)}
print(json.dumps({'aspis':[row(m,src,cache) for m in x['aspis']],'external':[row(m,math,math/'.lake/build/lib/lean') for m in x['external']]},sort_keys=True))'''
opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
proc=subprocess.run(['ssh',*opts,'dombarker@100.108.41.90','python3 -c '+shlex.quote(remote_py)],input=json.dumps(payload),text=True,capture_output=True,check=True)
# Strip SSH host-key informational messages; the JSON line is the final stdout record.
remote=json.loads(proc.stdout.strip().splitlines()[-1])
for row in local_rows:
 rem=next((x for x in remote['aspis'] if x['module']==row['module']),None)
 row['host_source_matches_local']=bool(rem and rem['source_exists'] and rem['source_sha256']==row['sha256'])
 row['host_olean_exists']=bool(rem and rem['olean_exists'])
 row['host_olean_sha256']=rem['olean_sha256'] if rem else None
ext_rows=remote['external']
for r in ext_rows:r['source_root']='/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib';r['cache_root']='/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib/.lake/build/lib/lean'
report={'start_module':START,'local_tracked_root':str(LEAN),'pinned_host_source_root':'/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','pinned_host_cache_root':'/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib','mathlib_source_root':'/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib','mathlib_commit':'9a04890da70b255c5e1b4da353fa697cf0dd3afe','local_recursive_aspis_module_count':len(seen),'missing_local_modules':missing,'all_host_sources_byte_match_local':all(x['host_source_matches_local'] for x in local_rows),'all_aspis_olean_present':all(x['host_olean_exists'] for x in local_rows),'aspis_modules':local_rows,'external_import_count':len(ext_rows),'external_direct_imports':ext_rows,'mathlib_api_sources':[],'tool_actions':{'Lean_compilation':False,'cache_mutation':False,'source_modification':False}}
api_dir=Path(__file__).parent/'mathlib-source/Mathlib/Algebra/Polynomial'
for rel in ['BigOperators.lean','Degree/Operations.lean','Degree/Defs.lean','Eval/Defs.lean']:
 p=api_dir/rel
 report['mathlib_api_sources'].append({'relative_path':'Mathlib/Algebra/Polynomial/'+rel,'local_copy':str(p.relative_to(Path(__file__).parent)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
api_cache={
 'BigOperators.lean':('61cedfb72e1df9e710242f654d5b05434ae5df7fcdbc16d2f0820fcd460fb989',115400),
 'Degree/Operations.lean':('5afab05643ab5eec60f9740a23c12c4d3190ebb12568d2f03dcfbfeeef81fa97',234960),
 'Degree/Defs.lean':('dc3c8c56bf1adecb02a0c5645119855f3ffc1f19f33fb171619b20379b728e87',201184),
 'Eval/Defs.lean':('3dd44d30060a79b4546309de79711ab1b630ee5701e01524d2d496df7928f40f',391568)}
for row,rel in zip(report['mathlib_api_sources'],['BigOperators.lean','Degree/Operations.lean','Degree/Defs.lean','Eval/Defs.lean']):
 module='Mathlib.Algebra.Polynomial.'+rel.removesuffix('.lean').replace('/','.')
 row.update({'module':module,'source_path':'/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/'+rel,'source_sha256':row['sha256'],'cache_path':'/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib/.lake/build/lib/lean/'+module.replace('.','/')+'.olean','olean_sha256':api_cache[rel][0],'olean_bytes':api_cache[rel][1],'imports':re.findall(r'^public?\s*import\s+([A-Za-z0-9_.]+)',(api_dir/rel).read_text(),re.M)})
report['api_name_findings']={
 'actual_names':{
  'natDegree_sum_le':'Mathlib.Algebra.Polynomial.BigOperators.lean:61-63; RHS is Finset.fold max 0 (natDegree ∘ f), not a sum of degrees.',
  'natDegree_sum_le_of_forall_le':'Mathlib.Algebra.Polynomial.BigOperators.lean:65-67; uniform upper bound form.',
  'natDegree_prod_le':'Mathlib.Algebra.Polynomial.BigOperators.lean:136-137; Finset product natDegree bounded by sum of factor natDegrees.',
  'natDegree_mul_le':'Mathlib.Algebra.Polynomial.Degree.Defs.lean:468; binary product bound, imported by Degree.Operations.',
  'eval_C':'Mathlib.Algebra.Polynomial.Eval.Defs.lean:283-284.',
  'eval_X':'Mathlib.Algebra.Polynomial.Eval.Defs.lean:295-296.',
  'eval_sum':'Mathlib.Algebra.Polynomial.Eval.Defs.lean:344-346; Polynomial.sum/coefficient decomposition form.',
  'eval_finsetSum':'Mathlib.Algebra.Polynomial.Eval.Defs.lean:348-350; finite sum form.',
  'eval_prod':'Mathlib.Algebra.Polynomial.Eval.Defs.lean:675-677; finite product form.'},
 'searched_but_not_found_in_pinned_polynomial_tree':['natDegree_finset_prod','natDegree_finset_sum_le'],
 'import_observation':'Finite-sum/product natDegree bounds are in Mathlib.Algebra.Polynomial.BigOperators, not Degree.Operations. Degree.Operations publicly imports Degree.Defs. Eval.Defs provides evaluation identities. Presence of sources and cached oleans does not assert active LEAN_PATH resolution.'}
out=Path(__file__).parent/'inventory.json';out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'local_aspis_modules':len(seen),'missing_local':missing,'all_source_matches':report['all_host_sources_byte_match_local'],'all_aspis_oleans_present':report['all_aspis_olean_present'],'external_direct_imports':len(ext_rows),'missing_external_source_or_olean':[x['module'] for x in ext_rows if not x['source_exists'] or not x['olean_exists']]},indent=2))
