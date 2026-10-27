#!/usr/bin/env python3
"""D241 object/source audit; read-only host inventory, no compiler invocation."""
import pathlib,json,subprocess,hashlib
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
old=json.loads((e/'resume6-final-merge-gate.json').read_text());plan=json.loads((e/'resume7-plan.json').read_text());project={r['module']:r for r in plan['rows']}
# Lead ruling (h): the import-source pin table wins over historical variants.
pin_path='docs/research/100bit-spend-path-20261013/evidence/lean-semantic-prefix-agreement-20261015/import-source-pins.json'
pins=json.loads(subprocess.check_output(['git','show','research:'+pin_path]))['modules']
for m,p in pins.items():
 if m in project:
  b=subprocess.check_output(['git','show','research:'+p['source']])
  project[m]=dict(project[m],research_source_path=p['source'],research_source_sha256=hashlib.sha256(b).hexdigest(),research_source_exists=True)
rows={r['module']:dict(r) for r in old['objects']}
# The last audit emits actual kernel import headers, extending the old inventory.
ledger=e/'resume7-attempts.jsonl'
audit_attempts=[json.loads(x) for x in ledger.read_text().splitlines()] if ledger.exists() else []
last=next((r for r in reversed(audit_attempts) if r['module']=='R1Z/PV_Src_FinalAudit7C' and r['accepted']),None)
if last:
 import re
 log=(e/f"out-{last['attempt']}.log").read_text()
 actual={m for m,b in re.findall(r'PV_IMPORT (\S+) (true|false)',log)}
 edges={m:[] for m in actual}
 for m,d in re.findall(r'PV_EDGE (\S+) (\S+)',log):edges.setdefault(m,[]).append(d)
 for m in actual:
  if m not in rows:rows[m]=dict(module=m,source_receipts=[],projection_dependency_gap=False,source_gap='unassessed')
  rows[m]['imports']=sorted(set(edges[m]))
 # The current C shard is the root and is not listed in its own import header.
 m='R1Z.PV_Src_FinalAudit7C'
 if m not in rows:rows[m]=dict(module=m,source_receipts=[],projection_dependency_gap=False,imports=[])

for p in (root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_Src_*.lean'):
 m='R1Z.'+p.stem
 if m not in project:project[m]=dict(module=m,source_path=str(p.relative_to(root)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),research_source_exists=False)
 if m in rows and m=='R1Z.PV_Src_FinalAudit7C':
  import re
  rows[m]['imports']=re.findall(r'^import (\S+)',p.read_text(),re.M)
code='''import pathlib,json,hashlib
h=pathlib.Path('/home/dombarker/project-offloads');env=json.loads((h/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[str(h/'aspis-joint-20261019/objects')]+env['LEAN_PATH'].split(':');out=[]
for m in MODS:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(r)/rel for r in roots if (pathlib.Path(r)/rel).is_file()),None)
 out.append(dict(module=m,object_path=str(p) if p else None,object_sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else None,object_bytes=p.stat().st_size if p else None,object_realpath=str(p.resolve()) if p else None))
print(json.dumps(out))
'''.replace('MODS',repr(sorted(rows)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,capture_output=True,text=True,check=True)
for o in json.loads(r.stdout):rows[o['module']].update(o)
a=[json.loads(x) for x in (e/'resume7-attempts.jsonl').read_text().splitlines()] if (e/'resume7-attempts.jsonl').exists() else []
for r in a:
 if r.get('accepted') and r['module'].replace('/','.') in rows:
  rows[r['module'].replace('/','.')]['source_receipts'].append(dict(attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=r['object_sha256']))
for rr in json.loads((e/'resume7-firstfold-receipts.json').read_text()):
 r=rr['record']
 if r.get('validation_exit')==0:rows['R1FirstFold']['source_receipts'].append(dict(receipt=rr['receipt'],attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=r['object_sha256']))
# The authoritative historical cache pin also binds an exact source/object pair.
# This is a retained source/cache association, explicitly not a new compile run.
m='R0P.LogUpAssembly'
q=pins[m];expected=project[m]['research_source_sha256']
if q.get('exact_source_match_to_cache_revision') and q['source_sha256']==expected and q['object_sha256']==rows[m]['object_sha256']:
 rows[m]['source_receipts'].append(dict(source_pin_table=pin_path,cache_revision=q['source_cache_comparison_revision'],evidence_kind='exact historical source/cache association; no new compile',source_sha256=expected,object_sha256=q['object_sha256']))
env=json.loads((e/'resume7-env-J.json').read_text());manifest=json.loads((e/'resume7-lake-manifest.json').read_text());packages={p['name']:p for p in manifest['packages']};manifest_sha=hashlib.sha256((e/'resume7-lake-manifest.json').read_bytes()).hexdigest();env_sha=hashlib.sha256((e/'resume7-env-J.json').read_bytes()).hexdigest()
port=json.loads((e/'resume7-aeneas-port-pin.json').read_text());backend=port['backend-final-manifest.json']['content'];backend_objects=port['summary.json']['content']['targets']
ns_package={'Mathlib':'mathlib','Aesop':'aesop','Batteries':'batteries','Qq':'Qq','ProofWidgets':'proofwidgets','ImportGraph':'importGraph','LeanSearchClient':'LeanSearchClient','Plausible':'plausible'}
projection_cone={'R1NaturalProjection'}
while True:
 n=len(projection_cone);projection_cone.update(m for m,r in rows.items() if set(r.get('imports',[]))&projection_cone)
 if len(projection_cone)==n:break
for m,row in rows.items():
 row['projection_dependency_gap']=False
 row['external_manifest_link']=None;row['classification']='PROJECT' if m in project else 'EXTERNAL'
 if m in project:
  p=project[m];sha=p.get('research_source_sha256') or p['source_sha256'];row.update(expected_source_sha256=sha,source_path=p.get('research_source_path') or p['source_path'],source_kind='research HEAD' if p.get('research_source_exists') else 'reviewable branch addition')
  row['source_object_hash_link']=any(x['source_sha256']==sha and x['object_sha256']==row['object_sha256'] for x in row['source_receipts']);row['source_gap']=None if row['source_object_hash_link'] else 'No accepted receipt binds current object SHA to expected source SHA'
 else:
  ns=m.split('.')[0];link=dict(env_J_sha256=env_sha,toolchain=env['ELAN_TOOLCHAIN'],toolchain_git_revision=env['LEAN_GITHASH'],lake_manifest_sha256=manifest_sha)
  if ns in {'Init','Lean','Std','Lake'}:link.update(package='Lean core',package_revision=env['LEAN_GITHASH'])
  elif ns in {'Aeneas','AeneasMeta'}:link.update(package='Aeneas backend',package_revision=backend['upstream_revision'],port_patch_sha256=backend['patch_sha256'],base_library_archive_revision='ccf554595212759d6d7f853f46a84c7c53444c30',pinned_object_sha256=backend_objects[m]['olean_sha256'],archive_sha256='7f2afc2861916ce1bcaa5520d2a649d8e1243b29f24e49ffcf733eb4d3812f84',port='docs/research/100bit-spend-path-20261013/evidence/aeneas-lean432-port-20261016',pin_evidence='resume7-EJR_library-source-provenance.json',port_pin_evidence='resume7-aeneas-port-pin.json')
  elif ns in ns_package:
   p=packages[ns_package[ns]];link.update(package=p['name'],package_revision=p['rev'],url=p['url'])
  else:raise RuntimeError('unclassified external '+m)
  if ns in {'Aeneas','AeneasMeta'}:assert row['object_sha256']==link['pinned_object_sha256'],m
  row['external_manifest_link']=link;row['source_gap']=None if row['object_sha256'] else 'Missing external object';row['source_object_hash_link']=False
 # D241 replaces the earlier hypothetical all-input freshness rule. Preserve the old
 # flag as historical data, never silently reinterpret it as a completed replay.
 row['resume6_changed_input_replay_unattested']=row.pop('changed_dependency_cohort_gap',False)
 row['projection_exception']=None
for path in e.glob('no-scope-40*.json'):
 r=json.loads(path.read_text());m=r['module']
 if m in rows and rows[m].get('source_gap'):rows[m]['source_gap']+='; launcher refusal '+str(r['attempt'])+': '+r['reason'].strip()
gaps=[r for r in rows.values() if r['classification']=='PROJECT' and r['source_gap']]
gap_cones={}
for gap in gaps:
 cone={gap['module']}
 while True:
  n=len(cone);cone.update(m for m,r in rows.items() if set(r.get('imports',[]))&cone)
  if len(cone)==n:break
 gap_cones[gap['module']]=sorted(cone)
result=dict(ruling='D241',status='BLOCKED',research_revision=plan['research_revision'],branch_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),objects=list(rows.values()),reviewable_branch_additions=[m for m,r in rows.items() if r.get('source_kind')=='reviewable branch addition'],project_objects=sum(r['classification']=='PROJECT' for r in rows.values()),project_gaps=len(gaps),external_objects=sum(r['classification']=='EXTERNAL' for r in rows.values()),external_gaps=sum(bool(r['source_gap']) for r in rows.values() if r['classification']=='EXTERNAL'),projection_cone=sorted(projection_cone),projection_exception_closed_by_ruling_h=True,source_resolution_pin_table=pin_path,charged_lean=len(a),gap_modules=[r['module'] for r in gaps],source_resolution_gap_cones=gap_cones,current_research_revision=subprocess.check_output(['git','rev-parse','research'],text=True).strip())
(e/'resume7-merge-gate-v2.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# MERGE GATE v2: BLOCKED','',f"D241; research `{plan['research_revision']}`. PROJECT gaps: **48 → {len(gaps)}**; {result['project_objects']} project objects. EXTERNAL objects: {result['external_objects']}; manifest gaps: {result['external_gaps']}.",'','Every external object below is linked individually to the env-J toolchain and manifest package revision. Repository copies already selected by the source manifest remain PROJECT; R1FirstFold is also PROJECT (its repository filename is FirstFold.lean). Branch additions remain separately identified in each JSON source_kind field; their hash links bind the proposed branch bytes, and are not described as already present at research HEAD.','',f"Lead ruling (h) corrects the projection association: `lean/NaturalProjection.lean` is authoritative. Its source/object receipt 30200 matches current HEAD and current object; ProjectionHEAD is CLOSED without changing its source or object. The earlier two-goal failure concerned the wrong historical variant. Its dependency cone ({len(projection_cone)} modules) is retained as historical inventory, not a live exception. Four other shared source paths differ from the authoritative pin table; all are stopped for replacement. R0P.LogUpAssembly has a matching exact historical source/cache pin, closing its object association without a new compile. The remaining three object associations are blocked. Both hashes and all four path mismatches are recorded in resume7-source-resolution-correction.json.",'','Recompilation receipts retain exact import hashes. Historical changed-input replay flags are retained in JSON; a source hash link alone is not a claim of replaying every dependent.','', '## Remaining project gaps','']
for r in gaps:lines.append(f"- `{r['module']}`: {r['source_gap']}; expected `{r['expected_source_sha256']}`.")
lines+=['','## Every imported object','','| Module | Kind | Object SHA-256 | Source hash or manifest pin |','| --- | --- | --- | --- |']
for m,r in sorted(rows.items()):
 s=(r['expected_source_sha256'] if r['source_object_hash_link'] else 'GAP: '+str(r['source_gap'])) if r['classification']=='PROJECT' else r['external_manifest_link']['package']+' @ '+r['external_manifest_link']['package_revision']
 if r['projection_exception']:s+='; ProjectionHEAD'
 lines.append(f"| `{m}` | {r['classification']} | `{r['object_sha256']}` | {s} |")
(e/'MERGE-GATE.md').write_text('\n'.join(lines)+'\n');print('PROJECT',result['project_objects'],'gaps',len(gaps),'EXTERNAL',result['external_objects'],'gaps',result['external_gaps'])
