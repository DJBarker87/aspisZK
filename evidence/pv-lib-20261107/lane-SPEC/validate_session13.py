"""Validate retained session13 evidence offline. Never launches Lean/a raw walk."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2];sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION13_STATUS.json').read_text())
assert s['base_revision']=='f794c7fe857c2dbf16aa1dc3268e40033f7316a9'
for k in ['full_task_complete','successful_original_history','full_source_joint_witness_inhabited','full_joint_contradiction_proved','physical_stack_pairing_proved','concrete_Values_binding_discharged','integrated_v2_source_adequacy_proved','full_contracts_rebound','nonvacuous_same_history_exports','hook454_bound','stack_size295_bound']:assert s[k] is False,k
assert s['entry_with_native_backing_pre_proved'] and s['local_C11_repair_installed']
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
assert len(s['accepted_focused'])==21 and len(s['failed_focused'])==14
assert set(s['accepted_focused']+s['failed_focused'])==set(range(55148,55183))
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
a=json.loads((L/'SESSION13_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION13_RAW_ROOTS.json').read_text());m=json.loads((L/'SESSION13_RAW_GRAPH_MANIFEST.json').read_text())
assert a['attempt']==55191 and a['exit']==0 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
assert a['roots']==roots['count']==len(m['roots'])==128
assert set(roots['roots'])=={v['root'] for v in m['roots']}
b=lzma.decompress((L/'SESSION13_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION13_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
g=json.loads(b)
for row in m['files']:assert sha(g[row['name']].encode())==row['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession12.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession13.lean').read_text();suffix=new[new.index('\n  let env ←'):]
assert suffix==old[old.index('\n  let env ←'):]
assert sha(suffix.encode())==roots['collector_suffix_sha256'] and sha(new.encode())==roots['driver_sha256']
expected=(L/'host_audit_s12.py').read_text().replace('55190','55191').replace('Session12','Session13').replace('SESSION12','SESSION13').replace('session12','session13').replace('host_audit_s12.py','host_audit_s13.py')
assert (L/'host_audit_s13.py').read_text()==expected
la=json.loads((L/'SESSION13_LANEA_INPUT.json').read_text());assert la['read_only'] and not la['complete_table'] and la['all_same'] and len(la['comparison'])==20
for mod,row in la['comparison'].items():assert row['same_as_session12'] and sha(subprocess.check_output(['git','show',la['revision']+':lean/'+mod+'.lean'],cwd=R))==row['sha256']
for row in json.loads((L/'SESSION13_PROVENANCE.json').read_text())['attempts']:
 if row['accepted']:assert sha(subprocess.check_output(['git','show',row['passing_source_commit']+':'+row['path']],cwd=R))==row['source_sha256']
subprocess.run(['python3',str(L/'session13_builder.py'),'--check'],cwd=R,check=True)
for p in L.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
# Include pending documentation/evidence changes in the write-boundary check.
paths=set(subprocess.check_output(['git','diff','--name-only',s['base_revision']],cwd=R,text=True).splitlines())
paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
for f in paths:assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for line in subprocess.check_output(['git','diff','--name-status',s['base_revision'],'HEAD','--','lean'],cwd=R,text=True).splitlines():assert line.startswith('A\t'),line
print('PASS session13: exact receipts/provenance, C11 local repair, one strict128-root audit; full task OPEN')
