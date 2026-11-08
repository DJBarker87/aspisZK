"""Offline validation only: no build, raw walk or regression is launched."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).parent;base='74f750e69d70d6a046c50266fb7c52dbb2916cc5'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
receipts=sorted([json.loads(p.read_text()) for p in E.glob('receipt-*.json')],key=lambda r:r['attempt'])
focused=[r for r in receipts if not r['runtime_audit']];audits=[r for r in receipts if r['runtime_audit']]
assert {r['attempt'] for r in focused}==set(range(55600,55674))
assert {r['attempt'] for r in audits}=={55690}
assert len(focused)==74 and sum(r['accepted'] for r in focused)==47
failed=[r for r in focused if not r['accepted']];assert len(failed)==27
for r in receipts:
 a=r['attempt'];turn=json.loads((E/f'turn-{a}.json').read_text());admit=json.loads((E/f'admission-{a}.json').read_text())
 assert turn['exit']==0 and 'STREAMB_SLOTS=3' in turn['command'][-1] and admit['allowed'] is True
 assert all(c in r['command'] for c in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['swaps']=='0' and r['source_revision'] and r['source_index_blob']
 assert int(r['peak_rss_kbytes'])<8*1024*1024
 assert sha(lzma.decompress((E/f'resolution-{a}.json.xz').read_bytes()))==r['resolution_sha256']
 assert subprocess.check_output(['git','show',r['source_index_blob']]) and subprocess.check_output(['git','cat-file','-t',r['source_revision']],text=True).strip()=='commit'
 if not r['runtime_audit']:assert r['command'][-1]=='7000'
 if not r['accepted']:
  assert sha(lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sum(q['source_sha256']==r['source_sha256'] for q in receipts)==1
 else:
  p=Path(r['source_path']);assert sha(p.read_bytes())==r['source_sha256']
  assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option (?:maxHeartbeats|maxRecDepth)',p.read_text())
  assert 'sorryAx' not in (E/f'out-{a}.log').read_text()
support=json.loads((E/'SUPPORT.json').read_text());manifest=json.loads((E/'AUDIT_ROOTS.json').read_text())
assert len(support)==46 and len(manifest['roots'])==len(set(manifest['roots']))==221
assert len({r['target'] for r in focused if r['accepted']})==47
for module in support:
 assert sha(Path(module['source']).read_bytes())==module['source_sha256']
 assert module['attempt'] in [r['attempt'] for r in focused if r['accepted']]
a=json.loads((E/'RAW_AUDIT.json').read_text());assert a['attempt']==55690
assert a['strict_pass'] and a['summary_mismatches']==a['unresolved']==0
assert a['receipt']['accepted'] and a['receipt']['exit']=='0' and a['root_count']==221
assert set(manifest['roots'])=={r['root'] for r in a['roots']}
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in a['roots'])
am=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());compressed=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();raw=lzma.decompress(compressed)
assert sha(compressed)==am['archive_sha256'] and sha(raw)==am['uncompressed_sha256']
assert (E/'RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()==sha(raw)
files=json.loads(raw)
for f in am['files']:
 if f['name'] in files:assert sha(files[f['name']].encode())==f['sha256']
pattern=r'    \(#\[.*?\],\n     #\[.*?\]\)'
r1=Path('lean/PV_LIB_A_Reaudit12S13.lean').read_text();r2=Path('lean/PV_LIB_A_RawAudit14.lean').read_text()
assert re.sub(pattern,'ARRAYS',r1,count=1,flags=re.S)==re.sub(pattern,'ARRAYS',r2,count=1,flags=re.S)
changes=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
allowed={'evidence/pv-lib-20261107/'+n for n in ['PLIB_MAP.json','PLIB_MAP.md','REMAINING.md']}
assert all(p in allowed or p.startswith('evidence/pv-lib-20261107/lane-A/') or p.startswith('lean/PV_LIB_A_') for p in changes)
newlean=[p for p in changes if p.startswith('lean/')];assert len(newlean)==47
for p in newlean:assert subprocess.run(['git','cat-file','-e',base+':'+p],capture_output=True).returncode!=0
for p in ['tools/pv-lib-20261107/run-thread-audit.py','lean/PV_LIB_A_DeferredActions.lean','lean/PV_LIB_A_StoreActionTable.lean']:
 assert Path(p).read_bytes()==subprocess.check_output(['git','show',base+':'+p])
p=Path('evidence/pv-lib-20261107/lane-A/focused-host-s11.py');old=subprocess.check_output(['git','show',base+':'+str(p)],text=True);new=p.read_text()
assert new.replace(' or 55600<=a<=55689','').replace(' or 55690<=a<=55699','')==old
p=Path('evidence/pv-lib-20261107/PLIB_MAP.json');before=json.loads(subprocess.check_output(['git','show',base+':'+str(p)]));after=json.loads(p.read_text())
assert before['counts']==after['counts'] and len(before['slots'])==len(after['slots'])==170
for old,new in zip(before['slots'],after['slots']):assert old=={k:v for k,v in new.items() if k!='session14_prefix_support'}
assert before=={k:([ {kk:vv for kk,vv in slot.items() if kk!='session14_prefix_support'} for slot in v] if k=='slots' else v) for k,v in after.items() if k!='lane_A_session14'}
assert all(d['status']=='DEFERRED-POST-TARGET' for d in after['lane_A_session11']['deferred'])
c=json.loads((E/'LANE_C_FINAL_INPUT.json').read_text())
for f in c['files']:
 raw=(E/f['copy']).read_bytes();assert sha(raw)==f['sha256']
 assert raw==subprocess.check_output(['git','show',c['revision']+':'+f['path']])
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024**2]
subprocess.run(['git','diff','--check'],check=True)
keys=['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256']
(E/'COMPILES.json').write_text(json.dumps([{k:r[k] for k in keys} for r in receipts],indent=2)+'\n')
result=dict(base=base,support_modules=46,new_roots=221,focused_scopes=74,accepted_focused=47,
 retained_failed_inputs=[r['attempt'] for r in failed],strict_new_attempt=55690,strict_new_roots=221,strict_pass=True,
 standard_axioms_only=True,all_scopes_capped_and_swap_zero=True,legacy_v2_unchanged=True,historical_slot_statuses_unchanged=True,
 deferred_post_target_unchanged=True,source_unchanged_after_audit=True,launcher_change='556xx allocation only',
 row_closures=0,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,byte_images_defined=0,
 next_lean='55674-55689',next_raw='55691-55699; new/changed inputs only',
 validation='PASS retained evidence/boundaries; requested completion NOT achieved; target not yet established')
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
