"""Offline session15 evidence check. Never launches Lean or a raw walk."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION15_STATUS.json').read_text())
assert s['base_revision']=='27fa457421791364e945ac744b1c8c70cbdfde72'
for k in ['full_task_complete','physical_stack_pairing_proved','native295_original_reachability_proved','native454_original_reachability_proved','full_Values_source_binding_discharged','successful_original_history_through_ThreadInit','integrated_v2_source_adequacy_proved','full_contracts_rebound','nonvacuous_same_history_exports','full_source_joint_witness_inhabited','full_joint_contradiction_proved','original278_consumed','host_scope_remaining']:assert s[k] is False,k
for k in ['entry_complete_pre_on_one_world','first_original_TLS_getter_reached_and_consumed','original277_reached_and_consumed','original278_reached_and_bound','source_trace_transport_applied','strict_pass']:assert s[k] is True,k
assert s['source_model_prefix_steps']==63 and s['native_answers_consumed_at63']==2
assert s['rows_closed']==0 and s['new_SPEC_C_finding'] is None
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
assert len(s['accepted_focused'])==30 and len(s['failed_focused'])==31
assert set(s['accepted_focused']+s['failed_focused'])==set(range(55455,55490))|set(range(55500,55526))
for a in s['accepted_focused']+s['failed_focused']:
 r=json.loads((L/f'receipt-{a}.json').read_text());p=R/'lean'/(r['target']+'.lean')
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert r['swaps']=='0' and r['source_revision'] and r['peak_rss_kbytes'] and r['wall']
 assert json.loads((L/f'admission-{a}.json').read_text())['allowed'] is True
 assert (L/f'resolution-{a}.json.xz').exists()
 if r['accepted']:
  assert r['exit']==0 and sha(p.read_bytes())==r['source_sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text())
  assert not any('sorryAx' in line for line in r['axioms_summary_based'])
 else:
  assert r['exit']!=0
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sha(p.read_bytes())!=r['source_sha256']
a=json.loads((L/'SESSION15_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION15_RAW_ROOTS.json').read_text());m=json.loads((L/'SESSION15_RAW_GRAPH_MANIFEST.json').read_text())
assert a['attempt']==55491 and a['exit']==0 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
r=json.loads((L/'receipt-55491.json').read_text())
assert r['accepted'] and r['exit']==0 and r['swaps']=='0'
for k in ['source_revision','wall','peak_rss_kbytes']:assert r[k]==a[k]
for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in r['command']
assert json.loads((L/'admission-55491.json').read_text())['allowed'] is True
assert not a['rerun'] and not a['walker_changes'] and not a['collector_changes']
assert a['roots']==roots['count']==len(m['roots'])==128
assert set(roots['roots'])=={v['root'] for v in m['roots']}
for row in m['roots']:
 assert row['equal'] and set(row['walked_axioms'])==set(row['summary_axioms'])
 assert set(row['walked_axioms'])<=set(['propext','Quot.sound','Classical.choice'])
b=lzma.decompress((L/'SESSION15_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION15_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
g=json.loads(b)
for row in m['files']:assert sha(g[row['name']].encode())==row['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession14.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession15.lean').read_text();suffix=new[new.index('\n  let env ←'):]
assert suffix==old[old.index('\n  let env ←'):]
assert sha(suffix.encode())==roots['collector_suffix_sha256'] and sha(new.encode())==roots['driver_sha256']
expected=(L/'host_audit_s14.py').read_text().replace('55490','55491').replace('Session14','Session15').replace('SESSION14','SESSION15').replace('session14','session15').replace('host_audit_s14.py','host_audit_s15.py')
assert (L/'host_audit_s15.py').read_text()==expected
assert (L/'host_attempt_s15.py').read_text().replace(' or 55500<=a<=55589','')==(L/'host_attempt_s14.py').read_text()
la=json.loads((L/'SESSION15_LANEA_INPUT.json').read_text());assert la['read_only'] and la['all_same'] and len(la['comparison'])==20
for mod,row in la['comparison'].items():assert row['same_as_session14'] and sha(subprocess.check_output(['git','show',la['revision']+':lean/'+mod+'.lean'],cwd=R))==row['sha256']
for row in json.loads((L/'SESSION15_PROVENANCE.json').read_text())['attempts']:
 if row['accepted']:assert sha(subprocess.check_output(['git','show',row['passing_source_commit']+':'+row['path']],cwd=R))==row['source_sha256']
t=json.loads((L/'SESSION15_TLS_SOURCE.json').read_text());raw=lzma.decompress(subprocess.check_output(['git','show',t['revision']+':'+t['source']],cwd=R));assert sha(raw)==t['llbc_sha256']
for p in L.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
paths=set(subprocess.check_output(['git','diff','--name-only',s['base_revision']],cwd=R,text=True).splitlines())
paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
for f in paths:assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for line in subprocess.check_output(['git','diff','--name-status',s['base_revision'],'HEAD','--','lean'],cwd=R,text=True).splitlines():assert line.startswith('A\t'),line
print('PASS session15: original63/2 consumed natives, exact provenance, strict128/128 exit0; full task OPEN')
