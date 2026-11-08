"""Offline validation of exact session12 evidence. Runs no Lean/raw audit."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2];sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION12_STATUS.json').read_text());assert s['base_revision'].startswith('966c9281519')
for k in ['full_task_complete','successful_original_history','full_source_joint_witness_inhabited','full_joint_contradiction_proved','physical_stack_pairing_proved','concrete_Values_binding_discharged','full_contracts_rebound','nonvacuous_same_history_exports','integrated_v2_source_adequacy_proved']:
 assert s[k] is False,k
assert s['scope_u8_repaired'] and s['local_stack_codec_repaired']
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
assert len(s['accepted_focused'])==21 and len(s['failed_focused'])==11
assert set(s['accepted_focused']+s['failed_focused'])==set(range(55116,55148))
for a in s['accepted_focused']+s['failed_focused']:
 r=json.loads((L/f'receipt-{a}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert r['swaps']=='0' and r['source_revision'] and r['peak_rss_kbytes'] and r['wall']
 assert json.loads((L/f'admission-{a}.json').read_text())['allowed'] is True
 assert (L/f'resolution-{a}.json.xz').exists()
 p=R/'lean'/(r['target']+'.lean')
 if a in s['accepted_focused']:
  assert r['accepted'] and r['exit']==0 and sha(p.read_bytes())==r['source_sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text())
  assert not any('sorryAx' in row for row in r['axioms_summary_based'])
 else:
  assert r['exit']!=0 and not r['accepted']
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sha(p.read_bytes())!=r['source_sha256']
a=json.loads((L/'SESSION12_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION12_RAW_ROOTS.json').read_text());m=json.loads((L/'SESSION12_RAW_GRAPH_MANIFEST.json').read_text())
assert a['attempt']==55190 and a['exit']==0 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
assert a['roots']==roots['count']==len(m['roots'])==159
assert set(roots['roots'])=={v['root'] for v in m['roots']}
b=lzma.decompress((L/'SESSION12_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION12_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
g=json.loads(b)
for row in m['files']:assert sha(g[row['name']].encode())==row['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession11.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession12.lean').read_text()
suffix=new[new.index('\n  let env ←'):];assert suffix==old[old.index('\n  let env ←'):]
assert sha(suffix.encode())==roots['collector_suffix_sha256'] and sha(new.encode())==roots['driver_sha256']
expected=(L/'host_audit_s11.py').read_text().replace('34993','55190').replace('Session11','Session12').replace('SESSION11','SESSION12').replace('session11','session12').replace('host_audit_s11.py','host_audit_s12.py')
assert (L/'host_audit_s12.py').read_text()==expected
la=json.loads((L/'SESSION12_LANEA_INPUT.json').read_text());assert la['read_only'] and not la['complete_table'] and la['all_same'] and len(la['comparison'])==20
for mod,row in la['comparison'].items():
 assert row['same_as_session11'] and sha(subprocess.check_output(['git','show',la['revision']+':lean/'+mod+'.lean'],cwd=R))==row['sha256']
abi=json.loads((L/'SESSION12_ABI_SOURCE.json').read_text())
assert sha(subprocess.check_output(['git','show',abi['source_revision']+':'+abi['atomic_source_path']],cwd=R))==abi['atomic_source_sha256']
for row in json.loads((L/'SESSION12_PROVENANCE.json').read_text())['attempts']:
 if row['accepted']:assert sha(subprocess.check_output(['git','show',row['passing_source_commit']+':'+row['path']],cwd=R))==row['source_sha256']
for p in L.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
for f in subprocess.check_output(['git','diff','--name-only',s['base_revision'],'HEAD'],cwd=R,text=True).splitlines():
 assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for line in subprocess.check_output(['git','diff','--name-status',s['base_revision'],'HEAD','--','lean'],cwd=R,text=True).splitlines():assert line.startswith('A\t'),line
print('PASS: session12 receipts, local C9/C10 repairs, one strict159-root audit; original physical history and full OwnInit task OPEN')
