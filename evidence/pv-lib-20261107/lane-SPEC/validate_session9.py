"""Verify retained source/receipt/graph evidence without rerunning Lean or raw audit."""
from pathlib import Path
import json,lzma,hashlib,re
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION9_STATUS.json').read_text())
assert not any(s[k] for k in ['full_task_complete','successful_original_history','full_source_joint_witness_inhabited','full_joint_contradiction_proved','integrated_v2_source_adequacy_proved','concrete_Values_binding_discharged'])
assert s['SPEC_C5_applied'] and s['checked_local_scope_allocation_gap']
assert not s['endpoint_premises_removed'] and not s['endpoint_premises_added'] and not s['T_changes']
for a in s['accepted_focused']+s['failed_focused']:
 r=json.loads((L/f'receipt-{a}.json').read_text())
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert r['source_revision'] and r.get('wall') and r.get('peak_rss_kbytes') and r['swaps']=='0'
 assert (L/f'resolution-{a}.json.xz').exists()
 if a in s['accepted_focused']:
  assert r['exit']==0 and r['accepted']
  assert sha((R/'lean'/(r['target']+'.lean')).read_bytes())==r['source_sha256']
  assert not any('sorryAx' in x for x in r['axioms_summary_based'])
 else:
  assert r['exit']!=0 and not r['accepted']
  assert sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  final=(R/'lean'/(r['target']+'.lean')).read_bytes()
  assert sha(final)!=r['source_sha256'], 'unchanged failed source'
replay=json.loads((L/'SESSION9_LANEA_REPLAY.json').read_text())
original=json.loads(lzma.decompress((L/'SESSION9_LANEA_REPLAY_SOURCES.json.xz').read_bytes()))
rename={row['original_module']:row['private_module'] for row in replay['modules']}
assert len(rename)==20
for row in replay['modules']:
 src=original[row['original_module']]
 actual=(R/'lean'/(row['private_module']+'.lean')).read_text()
 expected=re.sub(r'^import (\S+)',lambda z:'import '+rename.get(z[1],z[1]),src,flags=re.M)
 assert actual==expected
 assert sha(src.encode())==row['original_sha256'] and sha(actual.encode())==row['private_sha256']
input=json.loads((L/'SESSION9_LANEA_INPUT.json').read_text())
assert input['revision']==s['lanea_revision'] and input['read_only'] and not input['complete_table']
surface=json.loads(lzma.decompress((L/'SESSION9_LANEA_SOURCES.json.xz').read_bytes()))
assert all(sha(surface[m].encode())==h for m,h in input['source_pins'].items())
audit=json.loads((L/'SESSION9_RAW_AUDIT.json').read_text())
assert audit['attempt']==34991 and audit['exit']==0 and audit['all_equal'] and audit['unresolved']==0 and audit['standard_axioms_only']
roots=json.loads((L/'SESSION9_RAW_ROOTS.json').read_text())
manifest=json.loads((L/'SESSION9_RAW_GRAPH_MANIFEST.json').read_text())
assert audit['roots']==roots['count']==len(manifest['roots'])==123
assert set(roots['roots'])=={x['root'] for x in manifest['roots']}
data=lzma.decompress((L/'SESSION9_RAW_GRAPH_ARCHIVE.json.xz').read_bytes())
assert sha(data)==(L/'SESSION9_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
graphs=json.loads(data)
for row in manifest['files']:assert sha(graphs[row['name']].encode())==row['sha256']
base=(R/'lean/PV_LIB_SPEC_RawAuditSession8.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession9.lean').read_text()
base_tail=base[base.index('\n  let env ←'):];new_tail=new[new.index('\n  let env ←'):]
assert base_tail==new_tail and sha(new_tail.encode())==roots['collector_suffix_sha256']
old=(R/'lean/PV_LIB_SPEC_OwnInitFull.lean').read_text();new=(R/'lean/PV_LIB_SPEC_OwnInitCut92.lean').read_text()
start=old.index('def AllocationWitness');end=old.index('/-- There is NO Some premise.',start)
assert old[start:end].replace('body.drop 94','body.drop 92') in new
assert all(p.stat().st_size<=20*1024*1024 for p in L.iterdir() if p.is_file())
print('PASS: session9 retained receipts, import-only replays, cut92 replacement and single strict123-root audit; full history/joint witness remain OPEN')
