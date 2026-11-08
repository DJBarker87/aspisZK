"""Offline evidence validation; launches no Lean and repeats no raw audit."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION11_STATUS.json').read_text())
for k in ['full_task_complete','physical_stack_pairing_proved','successful_original_history','full_source_joint_witness_inhabited','full_joint_contradiction_proved','concrete_Values_binding_discharged','integrated_v2_source_adequacy_proved']:
 assert not s[k],k
assert s['callback_byte_suffix_installed'] and s['source_scalar_projections_installed'] and s['canonical_thread_word_repair']
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
assert set(s['accepted_focused']+s['failed_focused'])==set(range(44989,44999))|set(range(55100,55116))
for a in s['accepted_focused']+s['failed_focused']:
 r=json.loads((L/f'receipt-{a}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert r['swaps']=='0' and r['source_revision'] and r['peak_rss_kbytes'] and r['wall']
 assert (L/f'resolution-{a}.json.xz').exists()
 admission=json.loads((L/f'admission-{a}.json').read_text());assert admission['allowed'] is True
 if a in s['accepted_focused']:
  assert r['exit']==0 and r['accepted']
  b=(R/'lean'/(r['target']+'.lean')).read_bytes();assert sha(b)==r['source_sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',b.decode())
  assert not any('sorryAx' in x for x in r['axioms_summary_based'])
 else:
  assert r['exit']!=0 and not r['accepted']
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sha((R/'lean'/(r['target']+'.lean')).read_bytes())!=r['source_sha256']
a=json.loads((L/'SESSION11_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION11_RAW_ROOTS.json').read_text());m=json.loads((L/'SESSION11_RAW_GRAPH_MANIFEST.json').read_text())
assert a['attempt']==34993 and a['exit']==0 and a['all_equal'] and a['unresolved']==0 and a['standard_axioms_only']
assert a['roots']==roots['count']==len(m['roots'])==110
assert set(roots['roots'])=={x['root'] for x in m['roots']}
b=lzma.decompress((L/'SESSION11_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
assert sha(b)==(L/'SESSION11_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
g=json.loads(b)
for row in m['files']:assert sha(g[row['name']].encode())==row['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession10.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession11.lean').read_text()
suffix=new[new.index('\n  let env ←'):]
assert suffix==old[old.index('\n  let env ←'):] and sha(suffix.encode())==roots['collector_suffix_sha256']
assert sha(new.encode())==roots['driver_sha256']
old=(L/'host_attempt_s7.py').read_text();new=(L/'host_attempt_s11.py').read_text()
assert new==old.replace('assert 49700<=a<=49799 or 44900<=a<=44999','assert 49700<=a<=49799 or 44900<=a<=44999 or 55100<=a<=55189')
la=json.loads((L/'SESSION11_LANEA_INPUT.json').read_text());assert la['read_only'] and not la['complete_table'] and len(la['source_pins'])==20
for module,row in la['source_pins'].items():
 assert row['unchanged']
 assert sha(subprocess.check_output(['git','show',la['revision']+':lean/'+module+'.lean'],cwd=R))==row['sha256']
abi=json.loads((L/'SESSION11_ABI_SOURCE.json').read_text())
assert abi['types']['67']['layout'][0]['value']['variant_layouts'][0]['field_offsets']==[0,8]
assert abi['types']['130']['layout'][0]['value']['variant_layouts'][0]['field_offsets']==[24,0]
assert sha(subprocess.check_output(['git','show',abi['revision']+':'+abi['rust_path']],cwd=R))==abi['rust_sha256']
p=json.loads((L/'SESSION11_PROVENANCE.json').read_text())
for row in p['attempts']:
 if row['accepted']:assert sha(subprocess.check_output(['git','show',row['passing_source_commit']+':'+row['path']],cwd=R))==row['source_sha256']
for f in L.iterdir():
 if f.is_file():assert f.stat().st_size<=20*1024*1024,f
changed=subprocess.check_output(['git','diff','--name-only','aa8cfbe2f1b','HEAD'],cwd=R,text=True).splitlines()
for f in changed:assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for row in subprocess.check_output(['git','diff','--name-status','aa8cfbe2f1b','HEAD','--','lean'],cwd=R,text=True).splitlines():assert row.startswith('A\t'),row
print('PASS: session11 receipts, byte suffix/source projection graphs, Thread word repair, one strict110-root audit; full original history/joint task OPEN')
