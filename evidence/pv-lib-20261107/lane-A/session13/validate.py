"""Offline validation only: no Lean, raw walk or other build is launched."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).parent;base='6dbfb38c6d1102dd828a716e9412043febf6c0da'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
receipts=sorted([json.loads(p.read_text()) for p in E.glob('receipt-*.json')],key=lambda r:r['attempt'])
focused=[r for r in receipts if not r['runtime_audit']];audits=[r for r in receipts if r['runtime_audit']]
assert {r['attempt'] for r in focused}==set(range(55351,55390))
assert {r['attempt'] for r in audits}=={47498,47499}
assert len(focused)==39 and sum(r['accepted'] for r in focused)==29
failed=[r for r in focused if not r['accepted']];assert len(failed)==10
for r in receipts:
 a=r['attempt'];turn=json.loads((E/f'turn-{a}.json').read_text());admit=json.loads((E/f'admission-{a}.json').read_text())
 assert turn['exit']==0 and 'STREAMB_SLOTS=3' in turn['command'][-1] and admit['allowed'] is True
 assert all(c in r['command'] for c in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['swaps']=='0' and r['source_revision'] and r['source_index_blob']
 if not r['runtime_audit']:assert r['command'][-1]=='7000'
 if not r['accepted']:
  assert sha(lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sum(q['source_sha256']==r['source_sha256'] for q in receipts)==1
 else:
  p=Path(r['source_path']);assert sha(p.read_bytes())==r['source_sha256']
  assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option (?:maxHeartbeats|maxRecDepth)',p.read_text())
  assert 'sorryAx' not in (E/f'out-{a}.log').read_text()
support=json.loads((E/'SUPPORT.json').read_text());manifest=json.loads((E/'AUDIT_ROOTS.json').read_text())
assert len(support)==27 and len(manifest['roots'])==113
assert len(set(manifest['roots']))==113
for prefix,attempt,total in [('',47499,113),('REAUDIT12_',47498,90)]:
 a=json.loads((E/(prefix+'RAW_AUDIT.json')).read_text());m=json.loads((E/(prefix+'AUDIT_ROOTS.json')).read_text())
 assert a['attempt']==attempt and a['strict_pass'] and a['summary_mismatches']==a['unresolved']==0
 assert a['receipt']['accepted'] and a['receipt']['exit']=='0' and a['root_count']==total
 assert set(m['roots'])=={r['root'] for r in a['roots']}
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in a['roots'])
 am=json.loads((E/(prefix+'RAW_GRAPH_MANIFEST.json')).read_text());compressed=(E/(prefix+'RAW_GRAPH_ARCHIVE.json.xz')).read_bytes();raw=lzma.decompress(compressed)
 assert sha(compressed)==am['archive_sha256'] and sha(raw)==am['uncompressed_sha256']
 assert (E/(prefix+'RAW_GRAPH_ARCHIVE.json.sha256')).read_text().strip()==sha(raw)
 files=json.loads(raw)
 for f in am['files']:
  if f['name'] in files:assert sha(files[f['name']].encode())==f['sha256']
old_audit=json.loads(Path('evidence/pv-lib-20261107/lane-A/session12/RAW_AUDIT.json').read_text())
assert not old_audit['strict_pass'] and old_audit['receipt']['exit']=='1'
changes=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
allowed={'evidence/pv-lib-20261107/'+n for n in ['PLIB_MAP.json','PLIB_MAP.md','REMAINING.md']}
assert all(p in allowed or p.startswith('evidence/pv-lib-20261107/lane-A/') or p.startswith('lean/PV_LIB_A_') and (p.endswith('13.lean') or p=='lean/PV_LIB_A_Reaudit12S13.lean') for p in changes)
newlean=[p for p in changes if p.startswith('lean/')];assert len(newlean)==29
for p in newlean:assert subprocess.run(['git','cat-file','-e',base+':'+p],capture_output=True).returncode!=0
for p in ['evidence/pv-lib-20261107/lane-A/focused-host-s11.py','tools/pv-lib-20261107/run-thread-audit.py','lean/PV_LIB_A_DeferredActions.lean','lean/PV_LIB_A_StoreActionTable.lean']:
 assert Path(p).read_bytes()==subprocess.check_output(['git','show',base+':'+p])
pattern=r'    \(#\[.*?\],\n     #\[.*?\]\)'
r1=Path('lean/PV_LIB_A_Reaudit12S13.lean').read_text();r2=Path('lean/PV_LIB_A_RawAudit13.lean').read_text()
assert re.sub(pattern,'ARRAYS',r1,count=1,flags=re.S)==re.sub(pattern,'ARRAYS',r2,count=1,flags=re.S)
p=Path('evidence/pv-lib-20261107/PLIB_MAP.json');before=json.loads(subprocess.check_output(['git','show',base+':'+str(p)]));after=json.loads(p.read_text())
assert before['counts']==after['counts'] and len(before['slots'])==len(after['slots'])==170
for old,new in zip(before['slots'],after['slots']):assert old=={k:v for k,v in new.items() if k!='session13_prefix_support'}
assert before['lane_A_session11']['deferred']==after['lane_A_session11']['deferred']
assert all(d['status']=='DEFERRED-POST-TARGET' for d in after['lane_A_session11']['deferred'])
c=json.loads((E/'LANE_C_INPUT.json').read_text());assert sha((E/'LANE_C_HANDOFF.md').read_bytes())==c['sha256']
assert (E/'LANE_C_HANDOFF.md').read_bytes()==subprocess.check_output(['git','show',c['revision']+':'+c['path']])
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024**2]
subprocess.run(['git','diff','--check'],check=True)
keys=['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256']
(E/'COMPILES.json').write_text(json.dumps([{k:r[k] for k in keys} for r in receipts],indent=2)+'\n')
result=dict(base=base,support_modules=27,new_roots=113,focused_scopes=39,accepted_focused=29,
 retained_failed_inputs=[r['attempt'] for r in failed],strict_inherited_attempt=47498,strict_inherited_roots=90,
 strict_new_attempt=47499,strict_new_roots=113,all_strict_pass=True,original47497_exit1_unchanged=True,
 standard_axioms_only=True,all_scopes_capped_and_swap_zero=True,legacy_v2_unchanged=True,historical_slot_statuses_unchanged=True,
 deferred_post_target_unchanged=True,source13_unchanged_after_audit=True,
 row_closures=0,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,byte_images_defined=0,
 allocated_lean_ids_exhausted=True,next_raw_range='55090-55099 then55390-55399; new/changed inputs only',
 validation='PASS retained evidence/boundaries; requested completion NOT achieved; target not yet established')
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
