"""Validate retained session14 evidence offline. Never launches Lean/a raw walk."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2];sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION14_STATUS.json').read_text())
assert s['base_revision']=='453b405e6224f8ac97a5274f0f3f59b9c4afa6c6'
for k in ['full_task_complete','successful_original_history_through_ThreadInit','full_source_joint_witness_inhabited','full_joint_contradiction_proved','physical_stack_pairing_proved','full_Values_source_binding_discharged','integrated_v2_source_adequacy_proved','full_contracts_rebound','nonvacuous_same_history_exports','native295_original_reachability_proved','native454_original_reachability_proved']:assert s[k] is False,k
for k in ['entry_complete_pre_on_one_world','local_C12_repair_installed','native295_full_assembly_local_check','native454_full_assembly_local_check','concrete_partial_Values_installed']:assert s[k] is True,k
assert s['source_model_prefix_steps']==40 and s['native_answers_consumed_at40']==0
assert s['host_scope_remaining'] is False
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
assert len(s['accepted_focused'])==31 and len(s['failed_focused'])==24
assert set(s['accepted_focused']+s['failed_focused'])==set(range(55400,55455))
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
a=json.loads((L/'SESSION14_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION14_RAW_ROOTS.json').read_text());m=json.loads((L/'SESSION14_RAW_GRAPH_MANIFEST.json').read_text())
assert a['attempt']==55490 and a['exit']==0 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
r=json.loads((L/'receipt-55490.json').read_text())
assert r['accepted'] and r['exit']==0 and r['swaps']=='0'
assert r['source_revision']==a['source_revision'] and r['wall']==a['wall'] and r['peak_rss_kbytes']==a['peak_rss_kbytes']
for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in r['command']
assert json.loads((L/'admission-55490.json').read_text())['allowed'] is True
assert not a['rerun'] and not a['walker_changes'] and not a['collector_changes']
for row in m['roots']:
 assert row['equal'] and set(row['walked_axioms'])==set(row['summary_axioms'])
 assert set(row['walked_axioms'])<=set(['propext','Quot.sound','Classical.choice'])
assert a['roots']==roots['count']==len(m['roots'])==205
assert set(roots['roots'])=={v['root'] for v in m['roots']}
b=lzma.decompress((L/'SESSION14_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION14_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
g=json.loads(b)
for row in m['files']:assert sha(g[row['name']].encode())==row['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession13.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession14.lean').read_text();suffix=new[new.index('\n  let env ←'):]
assert suffix==old[old.index('\n  let env ←'):]
assert sha(suffix.encode())==roots['collector_suffix_sha256'] and sha(new.encode())==roots['driver_sha256']
expected=(L/'host_audit_s13.py').read_text().replace('55191','55490').replace('Session13','Session14').replace('SESSION13','SESSION14').replace('session13','session14').replace('host_audit_s13.py','host_audit_s14.py')
assert (L/'host_audit_s14.py').read_text()==expected
old_launcher=(L/'host_attempt_s11.py').read_text()
new_launcher=(L/'host_attempt_s14.py').read_text()
assert new_launcher.replace(' or 55400<=a<=55489','')==old_launcher
la=json.loads((L/'SESSION14_LANEA_INPUT.json').read_text());assert la['read_only'] and not la['complete_table'] and la['all_same'] and len(la['comparison'])==20
for mod,row in la['comparison'].items():assert row['same_as_session13'] and sha(subprocess.check_output(['git','show',la['revision']+':lean/'+mod+'.lean'],cwd=R))==row['sha256']
for row in json.loads((L/'SESSION14_PROVENANCE.json').read_text())['attempts']:
 if row['accepted']:assert sha(subprocess.check_output(['git','show',row['passing_source_commit']+':'+row['path']],cwd=R))==row['source_sha256']
for script in ['session14_kinds.py','session14_vector.py']:subprocess.run(['python3',str(L/script),'--check'],cwd=R,check=True)
for p in L.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
# Include pending documentation/evidence changes in the write-boundary check.
paths=set(subprocess.check_output(['git','diff','--name-only',s['base_revision']],cwd=R,text=True).splitlines())
paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
for f in paths:assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for line in subprocess.check_output(['git','diff','--name-status',s['base_revision'],'HEAD','--','lean'],cwd=R,text=True).splitlines():assert line.startswith('A\t'),line
print('PASS session14: exact receipts/provenance, C12 local repair, one strict205-root audit; full task OPEN')
