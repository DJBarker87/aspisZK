"""Check retained session-2 evidence; no Lean or raw audit is re-executed."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((E/'SESSION2_REPLAY_PINS.json').read_text())
accepted=[];failed=[]
for n in range(49713,49725):
 r=json.loads((E/f'receipt-{n}.json').read_text())
 assert r['cohort']=='w3' and r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64,'Lean_M':7000}
 if r['accepted']:
  if str(n) in pins:
   p=pins[str(n)];data=subprocess.check_output(['git','show',p['revision']+':'+p['path']])
  else:data=(Path('lean')/(r['target']+'.lean')).read_bytes()
  assert sha(data)==r['source_sha256']
  assert 'sorryAx' not in (E/f'out-{n}.log').read_text()
  accepted.append(r)
 else:
  assert sha(lzma.decompress((E/f'failed-{n}.lean.xz').read_bytes()))==r['source_sha256']
  failed.append(n)
m=json.loads((E/'SESSION2_RAW_GRAPH_MANIFEST.json').read_text());blob=(E/m['archive']).read_bytes();assert sha(blob)==m['archive_sha256']
raw=lzma.decompress(blob);assert sha(raw)==m['uncompressed_sha256'];archive=json.loads(raw)
for f in m['files']:assert sha(archive[f['name']].encode())==f['sha256']
manifest=json.loads((E/'SESSION2_AUDIT_ROOTS.json').read_text())
results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in (E/'out-49791-w3.log').read_text().splitlines() if l.startswith('NEP62_RESULT ')]
assert {r['root'] for r in results}==set(manifest['roots']) and len(results)==27
allowed={'propext','Classical.choice','Quot.sound'}; reconciled=[]
aux='PV_FN_THREAD_f361.Pre.mk'
printer=(E/'out-49724.log').read_text()
assert f"'{aux}' depends on axioms: [propext, Classical.choice, Quot.sound]" in printer
for r in results:
 assert set(r['walked_axioms'])<=allowed
 if r['equal']:
  assert r['summary_axioms']==r['walked_axioms'];continue
 reached=archive['NEP_pv-thread_'+r['root']+'_REACHABLE.txt'].splitlines()
 assert aux in reached
 union=set(r['summary_axioms'])|allowed
 assert union==set(r['walked_axioms'])
 reconciled.append({'root':r['root'],'reached_auxiliary':aux,'constructor_summary_attempt':49724,'summary_union':sorted(union),'matches_retained_raw':True})
assert len(reconciled)==6
receipt=json.loads((E/'receipt-49791.json').read_text());assert receipt['exit']==1 and not receipt['accepted']
report={'strict_raw_attempt':49791,'raw_process_exit':1,'raw_process_accepted':False,'raw_roots':27,'direct_summary_agreements':21,'constructor_summary_disagreements':6,'retained_graph_reconciliation':'PASS','reconciliation':reconciled,'raw_axioms':sorted(allowed),'unresolved':0,'qualification':'One strict raw process only. Exit1 preserved; six differences reconciled offline from the retained graph and focused Pre.mk summary, without modifying walker or re-running raw audit.','receipt':receipt,'roots':results}
(E/'SESSION2_RAW_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
index=json.loads((E/'CONTRACT_INDEX.json').read_text());assert index['full_frozen_contracts']==0
freeze=json.loads(subprocess.check_output(['git','show','5e397cb3878:evidence/pv-lib-20261107/FREEZE.json']))
for name,want in freeze['files'].items():assert sha(subprocess.check_output(['git','show','HEAD:evidence/pv-lib-20261107/'+name]))==want
paths=subprocess.check_output(['git','diff','--name-only','4fcc1573c69'],text=True).splitlines()
assert all(p.startswith('evidence/pv-lib-20261107/lane-SPEC/') or re.fullmatch(r'lean/PV_LIB_SPEC_.*\.lean',p) for p in paths)
for p in Path('lean').glob('PV_LIB_SPEC_*.lean'):assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^axiom ',p.read_text(),re.M)
summary={'session_start':'4fcc1573c6983a577ffcdc651b3f0726c3f95145','accepted_focused':accepted,'failed_elaborations':failed,'full_frozen_contracts':0,'normative_contracts':29,'full_joint_witnesses':0,'full_joint_contradictions':0,'new_local_machine_mismatch':'SPEC-C2, exact14320 OWNER registration omission','strict_raw_process_exit':1,'retained_raw_reconciliation':'PASS','new_raw_roots':27,'frozen_files_unchanged':len(freeze['files']),'write_boundary':'PASS','endpoint_premises_added':0,'endpoint_premises_removed':0,'target_established':False,'next_lean':49725,'next_raw':49792}
(E/'SESSION2_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'accepted_focused':len(accepted),'failed':failed,'raw_process_exit':1,'raw_reconciliation':'27/27','full_contracts':0,'full_joint_witnesses':0,'boundary':'PASS'}))
