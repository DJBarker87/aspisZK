"""Offline retained evidence checks; never launches Lean or repeats the raw walk."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION10_STATUS.json').read_text())
for key in ['full_task_complete','all_images_installed_and_source_bound','successful_original_history','full_source_joint_witness_inhabited','full_joint_contradiction_proved','concrete_Values_binding_discharged','integrated_v2_source_adequacy_proved']:
 assert not s[key],key
assert s['SPEC_C6_dispatch_repair_applied'] and s['checked_local_callback_byte_gap']
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
assert s['accepted_focused']+s['failed_focused'] and set(s['accepted_focused']+s['failed_focused'])==set(range(44969,44989))
for a in s['accepted_focused']+s['failed_focused']:
 r=json.loads((L/f'receipt-{a}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert r['source_revision'] and r.get('wall') and r.get('peak_rss_kbytes') and r['swaps']=='0'
 assert (L/f'resolution-{a}.json.xz').exists()
 if a in s['accepted_focused']:
  assert r['exit']==0 and r['accepted']
  source=(R/'lean'/(r['target']+'.lean')).read_bytes()
  assert sha(source)==r['source_sha256']
  assert not any('sorryAx' in line for line in r['axioms_summary_based'])
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source.decode())
 else:
  assert r['exit']!=0 and not r['accepted']
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sha((R/'lean'/(r['target']+'.lean')).read_bytes())!=r['source_sha256']
audit=json.loads((L/'SESSION10_RAW_AUDIT.json').read_text())
assert audit['attempt']==34992 and audit['exit']==0 and audit['all_equal'] and not audit['unresolved'] and audit['standard_axioms_only']
roots=json.loads((L/'SESSION10_RAW_ROOTS.json').read_text())
manifest=json.loads((L/'SESSION10_RAW_GRAPH_MANIFEST.json').read_text())
assert audit['roots']==roots['count']==len(manifest['roots'])==89
assert set(roots['roots'])=={row['root'] for row in manifest['roots']}
archive=lzma.decompress((L/'SESSION10_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
assert sha(archive)==(L/'SESSION10_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
graphs=json.loads(archive)
for row in manifest['files']:assert sha(graphs[row['name']].encode())==row['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession9.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession10.lean').read_text()
suffix=new[new.index('\n  let env ←'):]
assert suffix==old[old.index('\n  let env ←'):] and sha(suffix.encode())==roots['collector_suffix_sha256']
assert sha(new.encode())==roots['driver_sha256']
lanea=json.loads((L/'SESSION10_LANEA_INPUT.json').read_text())
assert lanea['read_only'] and not lanea['complete_table']
assert all(row['unchanged'] for row in lanea['source_pins'].values())
assert len(lanea['all_20_private_replay_sources_at_latest'])==20
assert all(row['unchanged'] for row in lanea['all_20_private_replay_sources_at_latest'])
for row in lanea['all_20_private_replay_sources_at_latest']:
 assert sha(subprocess.check_output(['git','show',lanea['revision']+':lean/'+row['module']+'.lean'],cwd=R))==row['sha256']
for f in L.iterdir():
 if f.is_file():assert f.stat().st_size<=20*1024*1024,f
changed=subprocess.check_output(['git','diff','--name-only','b98806b806c','HEAD'],cwd=R,text=True).splitlines()
for f in changed:
 assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_') or f in ['evidence/pv-lib-20261107/PSPEC_COMMON.md','evidence/pv-lib-20261107/SPEC_CORRECTIONS.md'],f
for row in subprocess.check_output(['git','diff','--name-status','b98806b806c','HEAD','--','lean'],cwd=R,text=True).splitlines():assert row.startswith('A\t'),row
print('PASS: retained session10 source/receipts, per-site evidence, unchanged v2 replay, one strict89-root audit; full history/joint task OPEN')
