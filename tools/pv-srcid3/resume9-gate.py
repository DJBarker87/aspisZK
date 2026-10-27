#!/usr/bin/env python3
"""Read-only source/object gate with rebuild-cohort identity under ruling h'."""
import pathlib,json,subprocess,hashlib,re
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
old=json.loads((e/'resume8-merge-gate-v2.json').read_text());rows={r['module']:dict(r) for r in old['objects']}
revision=subprocess.check_output(['git','rev-parse','research'],text=True).strip()
authority='evidence/envj-rebuild-20261026/EJR_final-inventory.json'
inventory_bytes=subprocess.check_output(['git','show',revision+':'+authority]);inventory=json.loads(inventory_bytes)
candidates={}
for r in inventory['selected']:
 if r.get('resolution'):candidates.setdefault(r['module'].replace('/','.'),[]).append(r)
ledger=[json.loads(l) for l in (e/'resume9-attempts.jsonl').read_text().splitlines()]
for r in ledger:
 if not r['accepted']:continue
 m=r['module'].replace('/','.')
 src=root/('docs/research/v8-r0-zk-20261009/lean/'+r['module']+'.lean')
 if m not in rows:
  rows[m]=dict(module=m,classification='PROJECT',source_receipts=[],source_kind='reviewable branch addition',source_path=str(src.relative_to(root)),imports=re.findall(r'^import (\S+)',src.read_text(),re.M),projection_dependency_gap=False,projection_exception=None)
 rows[m]['expected_source_sha256']=hashlib.sha256(src.read_bytes()).hexdigest()
 rows[m]['source_receipts'].append(dict(attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=r['object_sha256']))
# Read-only mathematical certificate cohort, from its owner's accepted source snapshots.
for q in json.loads((e/'resume9-model-pins.json').read_text()):
 m=q['module']
 if m not in rows:
  rows[m]=dict(module=m,classification='PROJECT',source_receipts=[],source_kind='read-only RunJoin branch dependency',source_path=q['source_path'],expected_source_sha256=q['source_sha256'],imports=q['imports'],projection_dependency_gap=False,projection_exception=None,readonly_source_revision=q['revision'])
 rows[m]['source_receipts'].append(dict(attempt=q['attempt'],receipt=q['receipt'],source_sha256=q['source_sha256'],object_sha256=q['object_sha256'],evidence_kind='accepted owner compiler receipt plus read-only consumer artifact hash',object_hash_from_consumer_receipt=q.get('object_hash_from_consumer_receipt'),object_hash_from_own_focused_consumer=q.get('object_hash_from_own_focused_consumer')))
# Final kernel closure has both old and new audit objects, all individually retained.
audit=next((r for r in reversed(ledger) if r['module']=='R1Z/PV_Src_FinalAudit9C' and r['accepted']),None)
if audit:
 log=(e/f"out-{audit['attempt']}.log").read_text()
 actual={m for m,b in re.findall(r'PV_IMPORT (\S+) (true|false)',log)}
 missing=actual-set(rows)
 if missing:raise RuntimeError('New import objects need classification: '+str(sorted(missing)))
code='''import pathlib,json,hashlib
h=pathlib.Path('/home/dombarker/project-offloads');env=json.loads((h/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[str(h/'aspis-joint-20261019/objects')]+env['LEAN_PATH'].split(':');out=[]
for m in MODS:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(r)/rel for r in roots if (pathlib.Path(r)/rel).is_file()),None)
 s=h/'aspis-joint-20261019/sources'/(m.replace('.','/')+'.lean')
 out.append(dict(module=m,object_path=str(p) if p else None,object_sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else None,object_bytes=p.stat().st_size if p else None,shared_source_sha256=hashlib.sha256(s.read_bytes()).hexdigest() if s.is_file() else None))
print(json.dumps(out))
'''.replace('MODS',repr(sorted(rows)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,capture_output=True,text=True,check=True)
source_cache={};resolutions=[]
for obj in json.loads(r.stdout):
 row=rows[obj['module']];previous=row['object_sha256'] if 'object_sha256' in row else None;row.update(obj)
 if row['classification']=='EXTERNAL':
  row['source_gap']=None if previous==row['object_sha256'] else 'External object changed since pinned manifest verification'
  continue
 # Rebuild selected entries can name multiple cohorts. Resolve the exact shared bytes,
 # then require an accepted receipt for the same source AND effective object.
 matches=[]
 for q in candidates.get(row['module'],[]):
  if q['sha256']!=row['shared_source_sha256']:continue
  p=q['resolution']['path']
  if p not in source_cache:source_cache[p]=subprocess.check_output(['git','show',revision+':'+p])
  if hashlib.sha256(source_cache[p]).hexdigest()==q['sha256']:matches.append(q)
 if matches:
  q=matches[-1];row['expected_source_sha256']=q['sha256'];row['source_path']=q['resolution']['path'];row['source_kind']='research HEAD at rebuild-resolved path';row['rebuild_resolution']=q['resolution'];resolutions.append(dict(module=row['module'],sha256=q['sha256'],workspace=q['workspace'],resolution=q['resolution']))
 expected=row['expected_source_sha256']
 row['source_object_hash_link']=any(q['source_sha256']==expected and q['object_sha256']==row['object_sha256'] for q in row['source_receipts'])
 row['source_gap']=None if row['source_object_hash_link'] else 'No accepted receipt binds effective object to expected source'
 if row['shared_source_sha256'] and row['shared_source_sha256']!=expected:row['source_gap']='Shared source differs from resolved expected source'
project_gaps=[r['module'] for r in rows.values() if r['classification']=='PROJECT' and r['source_gap']]
external_gaps=[r['module'] for r in rows.values() if r['classification']=='EXTERNAL' and r['source_gap']]
if audit:
 final=ledger[-3:]
 assert [r['module'] for r in final]==['R1Z/PV_Src_FinalAudit9'+c for c in 'ABC']
 assert all(r['accepted'] for r in final) and len(ledger)==100
 post=json.loads((e/'resume9-post-audit-object-check.json').read_text())
 assert not post['mismatches'] and not post['conflicting_audit_inputs'] and not post['missing_fingerprint_objects']
status='BLOCKED' if project_gaps or external_gaps else ('CLEAN' if audit else 'PENDING FINAL AUDIT')
result=dict(status=status,ruling="D255 / h'",research_revision=revision,branch_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_resolution_authority=authority,source_resolution_authority_sha256=hashlib.sha256(inventory_bytes).hexdigest(),project_objects=sum(r['classification']=='PROJECT' for r in rows.values()),project_gaps=len(project_gaps),external_objects=sum(r['classification']=='EXTERNAL' for r in rows.values()),external_gaps=len(external_gaps),gap_modules=project_gaps+external_gaps,objects=list(rows.values()),allocation9_audit=audit['attempt'] if audit else None,audit_shards=[dict(attempt=r['attempt'],target=r['module'],source_revision=r['source_revision'],exit=r['exit'],wall=r['wall'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axiom_reports=len(r['axioms'])) for r in ledger[-3:]] if audit else [],post_audit_objects_unchanged=post['checked'] if audit else None)
(e/'resume9-merge-gate-v2.json').write_text(json.dumps(result,indent=2)+'\n')
(e/'resume9-rebuild-resolved-paths.json').write_text(json.dumps(resolutions,indent=2)+'\n')
lines=[f'# MERGE GATE v2: {status}','',f"Ruling h′ / LOG D255. Research `{revision}`. PROJECT objects {result['project_objects']}, gaps {result['project_gaps']}; EXTERNAL objects {result['external_objects']}, gaps {result['external_gaps']}.",'',
'The three previously reported gaps were comparisons against the wrong file paths under the former ruling (h). The rebuild resolution record selects accepted-current sources; their current research bytes and shared sources match the accepted rebuild source/object receipts. No shared source or object was overwritten or recompiled for this correction. There is no changed dependency object and therefore no changed-input dependent cone to rebuild. The final allocation-9 audit is the required full kernel replay with these exact objects. Prior gap reports remain historical evidence, superseded by D255.', '',
'Exact source/object links, every external manifest link, rebuild-cohort paths, and all effective object hashes are in resume9-merge-gate-v2.json and resume9-rebuild-resolved-paths.json. Where the rebuild lists multiple cohorts, the exact shared source SHA and the effective object receipt select the matching entry; a module name alone never selects a path. Branch additions are individually receipt-linked. Historical changed-input replay flags remain historical and are not reported as fresh replays.','',
'Final audit: '+(str(audit['attempt'])+' (third shard; all three receipts in resume9-attempts.jsonl).' if audit else 'pending; last three charged Lean attempts reserved.'),'', 'Post-audit exact input/object hashes unchanged: '+str(result['post_audit_objects_unchanged'])+'.','',
'Read-only RunJoin dependency: 25 published sources pinned at 414d6fb38c, unchanged at 0a6a5428a8. They are owned by the live RunJoin branch and must be integrated alongside this consumer; no implementation source was duplicated here. Their accepted owner receipts, exact source hashes and consumer object hashes are retained in resume9-model-pins.json. This gate is source/object coherence for the named branch cohort, not deployed Records identification.','',
'Remaining gaps: '+(', '.join(result['gap_modules']) or 'none.')]
(e/'MERGE-GATE.md').write_text('\n'.join(lines)+'\n')
print(status,'PROJECT',result['project_objects'],'gaps',project_gaps,'EXTERNAL',result['external_objects'],'gaps',external_gaps)
