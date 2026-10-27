#!/usr/bin/env python3
"""Final fail-closed source/object gate from actual imported module headers."""
import pathlib,json,re,subprocess,hashlib
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';plan=json.loads((e/'resume6-plan.json').read_text());project={r['module']:dict(r) for r in plan['rows']}
a=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()];reject={r['attempt'] for r in json.loads((e/'resume6-rejected-profiles.json').read_text())}
final=next((r for r in reversed(a) if r['module']=='R1Z/PV_Src_FinalAudit6C'),None)
if final:
 log=(e/f"out-{final['attempt']}.log").read_text();mods={m:(b=='true') for m,b in re.findall(r'PV_IMPORT (\S+) (true|false)',log)};edges={m:[] for m in mods}
 for m,dep in re.findall(r'PV_EDGE (\S+) (\S+)',log):edges.setdefault(m,[]).append(dep)
 graph=dict(modules=[dict(module=m,has_data=b,imports=sorted(set(edges[m]))) for m,b in mods.items()],attempt=final['attempt'])
else:graph=json.loads((e/'resume6-binary-import-graph.json').read_text())
for p in (root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_Src_*.lean'):
 m='R1Z.'+p.stem
 if m not in project:project[m]=dict(module=m,source_path=str(p.relative_to(root)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),research_source_exists=False,research_source_sha256=None,research_source_path=None)
 if m not in {r['module'] for r in graph['modules']}:
  graph['modules'].append(dict(module=m,has_data=True,imports=['Init']+re.findall(r'^import (\S+)',p.read_text(),re.M),own_root_added=True))
(e/'resume6-final-binary-import-graph.json').write_text(json.dumps(graph,indent=2)+'\n')
mods=sorted(r['module'] for r in graph['modules'])
code='''import pathlib,json,hashlib
h=pathlib.Path('/home/dombarker/project-offloads');j=h/'aspis-joint-20261019';env=json.loads((h/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[str(j/'objects')]+env['LEAN_PATH'].split(':');out=[]
for m in MODS:
 rel=m.replace('.','/');obj=next((pathlib.Path(r)/(rel+'.olean') for r in roots if (pathlib.Path(r)/(rel+'.olean')).is_file()),None);src=j/'sources'/(rel+'.lean')
 out.append(dict(module=m,object_path=str(obj) if obj else None,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj else None,object_bytes=obj.stat().st_size if obj else None,host_source_sha256=hashlib.sha256(src.read_bytes()).hexdigest() if src.is_file() else None))
print(json.dumps(out))
'''.replace('MODS',repr(mods))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True);objects={r['module']:r for r in json.loads(r.stdout)}
# Reuse the recorded research and own source/object receipt index; add this allocation.
prior=json.loads((e/'resume6-project-provenance.json').read_text());receipts={}
for r in prior['project_modules']:
 for x in r['object_source_receipts']:receipts.setdefault((r['module'],x['object_sha256']),[]).append(x)
for r in a:
 if r['exit'] or r['nonstandard_axioms'] or not r['axiom_reports_complete'] or r['attempt'] in reject:continue
 if r.get('object_sha256'):receipts.setdefault((r['module'].replace('/','.'),r['object_sha256']),[]).append(dict(attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=r['object_sha256']))
initial={r['module']:r for r in json.loads((e/'resume6-package-closure.json').read_text())['objects']}
changed={m for m,r in objects.items() if m in initial and r['object_sha256']!=initial[m]['object_sha256']}
edges={r['module']:r['imports'] for r in graph['modules']}
projection_taint={'R1NaturalProjection'}
while True:
 n=len(projection_taint);projection_taint.update(m for m,deps in edges.items() if set(deps)&projection_taint)
 if n==len(projection_taint):break
affected=set(changed)
while True:
 n=len(affected);affected.update(m for m,deps in edges.items() if set(deps)&affected)
 if n==len(affected):break
path_module={r['object_path']:m for m,r in objects.items() if r['object_path']}
path_module.update({r['object_path']:m for m,r in initial.items() if r.get('object_path')})
for m in mods:path_module['/home/dombarker/project-offloads/aspis-joint-20261019/objects/'+m.replace('.','/')+'.olean']=m
fresh=set()
for r in a:
 m=r['module'].replace('/','.')
 if r['exit'] or r['nonstandard_axioms'] or r['attempt'] in reject or m not in objects or r.get('object_sha256')!=objects[m]['object_sha256']:continue
 if 'complete binary transitive' not in r.get('dependency_resolution',''):continue
 ok=True
 for line in r['dependency_objects']:
  bits=line.split(maxsplit=1)
  if len(bits)!=2 or len(bits[0])!=64:ok=False;break
  dep=path_module.get(bits[1])
  if dep is None or objects[dep]['object_sha256']!=bits[0]:ok=False;break
 if ok:fresh.add(m)
cohort_gap=affected-fresh
rows=[]
for m in mods:
 q=project.get(m);o=objects[m];matches=receipts.get((m,o['object_sha256']),[]);row=dict(o,source_receipts=matches,imports=edges.get(m,[]))
 if q:
  expected=q.get('research_source_sha256') or q['source_sha256'];row.update(expected_source_sha256=expected,source_kind='research HEAD' if q.get('research_source_exists') else 'reviewable branch addition',source_path=q.get('research_source_path') or q['source_path'])
  row['source_object_hash_link']=any(x['source_sha256']==expected for x in matches)
  row['source_gap']=None if row['source_object_hash_link'] else 'No accepted receipt binds the current object SHA to the expected source SHA'
 else:row.update(source_kind='external package/toolchain',source_gap='No research HEAD source mapping and compiled-source/object hash receipt attested in this allocation',source_object_hash_link=False)
 row['changed_from_initial']=m in changed
 row['projection_dependency_gap']=m in projection_taint
 row['changed_dependency_cohort_gap']=m in cohort_gap
 rows.append(row)
# Complete reconstruction was not achieved even if the axiom shards pass.
audits=[r for r in a if r['module'].startswith('R1Z/PV_Src_FinalAudit6')]
result=dict(status='BLOCKED',research_revision=plan['research_revision'],branch_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),objects=rows,changed_objects=sorted(changed),projection_cone=sorted(projection_taint),changed_dependency_cohort_gaps=sorted(cohort_gap),audits=audits,charged_lean=len(a),source_object_links=sum(r['source_object_hash_link'] for r in rows),source_object_gaps=sum(bool(r['source_gap']) for r in rows),dependency_cohort_complete=False,reason='Protected projection source replay and/or its full downstream cohort remains unaccepted; full package compilation provenance and all changed-object dependent replays are incomplete within the allocation')
(e/'resume6-final-merge-gate.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# MERGE GATE: BLOCKED','',f"Pinned research: `{plan['research_revision']}`. See resume6-current-head-comparison.json for the final HEAD comparison.",'','This is not a clean ordered research-HEAD dependency rebuild. Standard axiom','reports alone do not establish that gate. Every enumerated imported object is','listed below with its accepted source hash link or an exact provenance gap.','Branch additions are explicitly distinguished from existing research sources.','',f"Actual binary closure: {len(rows)} objects. Accepted source/object hash links: {result['source_object_links']}; remaining source provenance gaps: {result['source_object_gaps']}.",'', 'R1NaturalProjection was tested from exact HEAD, not replaced by the passing','PV_Src_ProjectionProofs clone. The unapplied protected-source repair is in','PROJECTION-REPAIR.patch. Complete dependent replay is still required. The','precise projection cone and changed-object lists are in the companion JSON.','', 'The older Fmt profile and its nonstandard sampler output were quarantined;','pre-existing objects were restored. The repaired HEAD formatter was rebuilt','and checked with an empty axiom set. Rejected outputs are never source links.','', '## Full axiom audit','', '| ID | Target | Kernel exit | Standard reports | Wall | RSS KiB | Swap | Revision |','| --- | --- | --- | --- | --- | --- | --- | --- |']
for r in audits:lines.append(f"| {r['attempt']} | {r['module']} | {r['exit']} | {len(r['axioms']) if not r['nonstandard_axioms'] else 'REJECTED '+str(r['nonstandard_axioms'])} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} |")
lines+=['','## Recompiled objects','','Every charged target and rejected attempt is listed in RESUME6-RECEIPTS.md;','exact source/input hashes and complete axiom/error reports are in','resume6-attempts.jsonl. The accepted current object list, including sources,','is machine-readable in resume6-final-merge-gate.json.','', '## Every imported object','', '| Module | Current object SHA-256 | Compiled source SHA = HEAD SHA, or exact gap |','| --- | --- | --- |']
for r in rows:
 if r['source_object_hash_link']:s=f"`{r['expected_source_sha256']}` = {r['source_kind']}"
 else:s='GAP: '+r['source_gap']+('; expected `'+r['expected_source_sha256']+'`' if r.get('expected_source_sha256') else '')
 if r['projection_dependency_gap']:s+='; GAP: projection dependency cohort not certified current'
 if r['changed_dependency_cohort_gap']:s+='; GAP: complete changed-input dependency replay not attested'
 lines.append(f"| `{r['module']}` | `{r['object_sha256'] or 'MISSING'}` | {s} |")
(e/'MERGE-GATE.md').write_text('\n'.join(lines)+'\n');print('BLOCKED',len(rows),'objects;',result['source_object_links'],'links;',result['source_object_gaps'],'source gaps;',len(a),'charged attempts')
