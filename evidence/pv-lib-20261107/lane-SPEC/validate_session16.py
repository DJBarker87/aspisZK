"""Offline provenance/evidence checks only; no Lean or raw replay."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
L=Path(__file__).resolve().parent;R=L.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((L/'SESSION16_STATUS.json').read_text())
assert s['base_revision']=='ad69c95986e0c298959af938047d9199fc3d83a7'
assert s['source_model_prefix_steps']==85 and s['native_answers_consumed_at85']==5
for k in ['full_task_complete','physical_stack_pairing_proved','stack_grant_proved','native295_original_reachability_proved','native454_original_reachability_proved','full_Values_source_binding_discharged','successful_original_history_through_ThreadInit','integrated_v2_source_adequacy_proved','full_contracts_rebound','nonvacuous_same_history_exports','full_source_joint_witness_inhabited','full_joint_contradiction_proved','replacement_original_history_reached','host_scope_remaining','loops_unrolled','lane_a_joins_available']:assert s[k] is False,k
for k in ['original278_consumed','original279_consumed','original_forwarded18_consumed','replacement_graph_checked','binary_stack_coordinate_arithmetic_checked','entry_complete_pre_on_one_world','strict_pass']:assert s[k] is True,k
assert s['new_SPEC_C_finding'] is None and s['rows_closed']==0
assert not s['endpoint_premises_added'] and not s['endpoint_premises_removed'] and not s['T_changes']
assert len(s['accepted_focused'])==31 and len(s['failed_focused'])==17
assert set(s['accepted_focused']+s['failed_focused'])==set(range(55526,55574))
for a in s['accepted_focused']+s['failed_focused']:
 r=json.loads((L/f'receipt-{a}.json').read_text());p=R/'lean'/(r['target']+'.lean')
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 assert r['swaps']=='0' and r['source_revision'] and r['wall'] and r['peak_rss_kbytes']
 assert json.loads((L/f'admission-{a}.json').read_text())['allowed'] is True
 assert (L/f'resolution-{a}.json.xz').exists()
 if r['accepted']:
  assert r['exit']==0 and sha(p.read_bytes())==r['source_sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()),p
  assert not any('sorryAx' in x for x in r['axioms_summary_based'])
 else:
  assert r['exit']!=0 and sha(lzma.decompress((L/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sha(p.read_bytes())!=r['source_sha256']
for r in json.loads((L/'SESSION16_PROVENANCE.json').read_text())['attempts']:
 if r['accepted']:assert sha(subprocess.check_output(['git','show',r['passing_source_commit']+':'+r['path']],cwd=R))==r['source_sha256']
a=json.loads((L/'SESSION16_RAW_AUDIT.json').read_text());roots=json.loads((L/'SESSION16_RAW_ROOTS.json').read_text());m=json.loads((L/'SESSION16_RAW_GRAPH_MANIFEST.json').read_text());receipt=json.loads((L/'receipt-55492.json').read_text())
assert a['attempt']==55492 and a['exit']==0 and a['all_equal'] and a['standard_axioms_only'] and a['unresolved']==0
assert a['roots']==roots['count']==len(m['roots'])==127
assert set(roots['roots'])=={r['root'] for r in m['roots']}
assert receipt['accepted'] and receipt['exit']==0 and receipt['swaps']=='0'
for k in ['source_revision','wall','peak_rss_kbytes']:assert receipt[k]==a[k]
for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert cap in receipt['command']
assert json.loads((L/'admission-55492.json').read_text())['allowed'] is True
assert not a['rerun'] and not a['walker_changes'] and not a['collector_changes']
for r in m['roots']:
 assert r['equal'] and set(r['walked_axioms'])==set(r['summary_axioms'])
 assert set(r['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
b=lzma.decompress((L/'SESSION16_RAW_GRAPH_ARCHIVE.json.xz').read_bytes());assert sha(b)==(L/'SESSION16_RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()
g=json.loads(b)
for f in m['files']:assert sha(g[f['name']].encode())==f['sha256']
old=(R/'lean/PV_LIB_SPEC_RawAuditSession15.lean').read_text();new=(R/'lean/PV_LIB_SPEC_RawAuditSession16.lean').read_text();suffix=new[new.index('\n  let env ←'):]
assert suffix==old[old.index('\n  let env ←'):]
assert sha(suffix.encode())==roots['collector_suffix_sha256'] and sha(new.encode())==roots['driver_sha256']
assert (L/'host_attempt_s16.py').read_bytes()==(L/'host_attempt_s15.py').read_bytes()
la=json.loads((L/'SESSION16_LANEA_INPUT.json').read_text());assert la['read_only'] and la['all_same'] and not la['joins_available'] and len(la['comparison'])==20
for mod,v in la['comparison'].items():assert sha(subprocess.check_output(['git','show',la['revision']+':lean/'+mod+'.lean'],cwd=R))==v['sha256']
for f,h in json.loads((L/'SESSION16_STACK_SOURCE.json').read_text())['files'].items():assert sha((L/f).read_bytes())==h
paths=set(subprocess.check_output(['git','diff','--name-only',s['base_revision']],cwd=R,text=True).splitlines())
paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
for f in paths:assert f.startswith('evidence/pv-lib-20261107/lane-SPEC/') or f.startswith('lean/PV_LIB_SPEC_'),f
for line in subprocess.check_output(['git','diff','--name-status',s['base_revision'],'HEAD','--','lean'],cwd=R,text=True).splitlines():assert line.startswith('A\t'),line
for p in L.iterdir():
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
assert 'pv-lib-spec-' not in (L/'SESSION16_FINAL_SCOPES.txt').read_text()
print('PASS session16: original85 / 5 consumed natives; strict127/127 exit0; exact provenance and write boundary; full task OPEN')
