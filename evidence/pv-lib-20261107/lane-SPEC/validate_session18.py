"""Offline source/evidence integrity gate. No proof/audit/build is re-executed."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION18_STATUS.json').read_text());pv=json.loads((L/'SESSION18_PROVENANCE.json').read_text())
assert s['base_revision']=='68795ef34cb758c72f9c544dd64bd581cc19fa68'
assert not any(s[k] for k in ['full_task_complete','universal_contracts_inhabited','values_suffix_full_coverage_proved','reached_8248_295_454_proved','full_source_joint_witness_inhabited','conditional_only_on_laneA_joins_proved','full_joint_contradiction_proved','endpoint_premises_added','endpoint_premises_removed','T_changes'])
assert s['source_model_prefix_steps']==85 and s['native_answers_consumed_at85']==5
assert s['entry_rebase_performed'] and s['entry_stack_grant_inhabited'] and s['values_prefix_no_writer_before85']
assert s['new_findings']==['SPEC-C16','SPEC-C17'] and s['contracts_module']=='PV_LIB_SPEC_ContextFinalContracts18'
assert len(s['accepted_focused'])==67 and len(s['failed_focused'])==13 and s['admission_refusals']==[55778]
assert set(s['accepted_focused']+s['failed_focused']+s['admission_refusals'])==set(range(55700,55781))
for a in range(55700,55781):
 r=json.loads((L/f'receipt-{a}.json').read_text());v=next(x for x in pv['attempts'] if x['attempt']==a)
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert re.fullmatch('[0-9a-f]{40}',v['source_parent_revision'])
 admission=json.loads((L/f'admission-{a}.json').read_text())
 if r['class']=='admission':
  assert a==55778 and r['exit']==78 and not r['accepted'] and admission['allowed'] is False
  continue
 assert admission['allowed'] is True and r['swaps']=='0' and r['wall'] and r['peak_rss_kbytes']
 if r['accepted']:
  p=R/v['path'];assert sha(p.read_bytes())==r['source_sha256']
  assert sha(subprocess.check_output(['git','show',v['passing_source_commit']+':'+v['path']],cwd=R))==r['source_sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text())
  assert not any('sorryAx' in x for x in r['axioms_summary_based'])
 else:
  assert r['exit']!=0
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sha((R/v['path']).read_bytes())!=r['source_sha256']
fix=json.loads((L/'receipt-55733-CORRECTION.json').read_text());assert fix['erroneous_launcher_revision']=='d370d0a' and fix['effective_source_revision']=='528052a351c63911579a9d21cc6ccf662f110d78'
stop=json.loads((L/'receipt-55494.json').read_text());assert stop['exit']==241 and not stop['accepted']
assert json.loads((L/'SESSION18_DRAFT_AUDIT.json').read_text())['earns_no_pass']
assert json.loads((L/'SESSION18_DRAFT_GRAPH_STATUS.json').read_text())['files']==167
b=lzma.decompress((L/'SESSION18_DRAFT_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION18_DRAFT_GRAPH_ARCHIVE.json.sha256').read_text().strip()
roots=json.loads((L/'SESSION18_RAW_ROOTS.json').read_text());assert roots['count']==len(set(roots['roots']))==532 and len(roots['modules'])==63
assert [len(p['roots']) for p in roots['partitions']]==[178,178,176]
old=(R/'lean/PV_LIB_SPEC_RawAuditSession17.lean').read_text();suffix=old[old.index('\n  let env ←'):]
assert sha(suffix.encode())==roots['collector_suffix_sha256']
for part in roots['partitions']:
 p=R/'lean'/(part['driver']+'.lean');source=p.read_text()
 assert sha(p.read_bytes())==part['driver_sha256'] and source[source.index('\n  let env ←'):]==suffix
assert {r for p in roots['partitions'] for r in p['roots']}==set(roots['roots'])
a=json.loads((L/'SESSION18_RAW_AUDIT.json').read_text());m=json.loads((L/'SESSION18_RAW_GRAPH_MANIFEST.json').read_text());r=json.loads((L/'receipt-55495.json').read_text())
assert a['attempt']==55495 and a['exit']==0 and a['all_equal'] and a['standard_axioms_only'] and a['unresolved']==0
assert a['roots']==len(m['roots'])==532 and set(roots['roots'])=={x['root'] for x in m['roots']}
assert r['accepted'] and r['exit']==0 and r['swaps']=='0' and r['sequential_partitions']==3 and r['lean_timeout_seconds_each']==600 and r['aggregate_timeout_seconds']==1200
for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in r['command']
for k in ['source_revision','wall','peak_rss_kbytes','swaps']:assert r[k]==a[k]
assert not a['walker_changes'] and not a['collector_changes'] and not a['rerun'] and a['prior_stopped_attempt']==55494
assert s['strict_audit_passed'] and not s['strict_audit_pending'] and s['rows_closed']==0
for x in m['roots']:
 assert x['equal'] and set(x['walked_axioms'])==set(x['summary_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
b=lzma.decompress((L/'SESSION18_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION18_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip();g=json.loads(b)
for f in m['files']:assert sha(g[f['name']].encode())==f['sha256']
la=json.loads((L/'SESSION18_LANEA_INPUT.json').read_text());assert la['read_only'] and la['all_same'] and la['four_targets_all_open'] and not la['joins_available']
for mod,v in la['comparison'].items():assert sha(subprocess.check_output(['git','show',la['revision']+':lean/'+mod+'.lean'],cwd=R))==v['sha256']
for row in ['361','270','166','15','208','220','316','318','219','125','6','170','17','5','2','1','0','OwnInit']:
 stem='OwnInit18' if row=='OwnInit' else 'F'+row+'18'
 t=(R/'lean'/('PV_LIB_SPEC_ContextFinal'+stem+'.lean')).read_text()
 assert 'pre_same' in t and 'CounterBefore' in t and 'PV_LIB_SPEC_ContextMachine18.observe' not in t
paths=set(subprocess.check_output(['git','diff','--name-only',s['base_revision']],cwd=R,text=True).splitlines());paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
for f in paths:assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for line in subprocess.check_output(['git','diff','--name-status',s['base_revision'],'HEAD','--','lean'],cwd=R,text=True).splitlines():assert line.startswith('A\t'),line
for p in L.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
assert 'pv-lib-spec-' not in (L/'SESSION18_FINAL_SCOPES.txt').read_text()
print('PASS session18: strict532/532 exit0; exact retained failed/stopped/refused evidence; SPEC-C16/C17 repaired; complete target NOT established')
