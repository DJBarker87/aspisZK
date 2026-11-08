"""Offline source/retained-evidence validation. Launches no proof job."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).parent
base='8abdcb48c52faeeb43f3f6144aed586a6a2569f4'
sha=lambda b:hashlib.sha256(b).hexdigest()
support=json.loads((E/'SUPPORT.json').read_text());manifest=json.loads((E/'AUDIT_ROOTS.json').read_text());audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert len(support)==20 and len(manifest['roots'])==90
assert audit['strict_raw'] and audit['unresolved']==0 and audit['summary_mismatches']==1 and not audit['strict_pass']
assert set(manifest['roots'])=={r['root'] for r in audit['roots']}
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in audit['roots'])
assert [r['root'] for r in audit['roots'] if not r['equal']]==['PV_LIB_A_F6Constructors12.counter']
reconciliation=json.loads((E/'RAW_RECONCILIATION.json').read_text())
assert reconciliation['offline_augmented_agreements']==90 and reconciliation['original_exit']==1
assert all(r['equal'] and set(r['augmented_summary_axioms'])==set(r['walked_axioms']) for r in reconciliation['roots'])
for s in support:
 r=json.loads((E/f"receipt-{s['attempt']}.json").read_text());p=Path(s['source'])
 assert r['accepted'] and sha(p.read_bytes())==r['source_sha256']==s['source_sha256']
 assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option (?:maxHeartbeats|maxRecDepth)',p.read_text())
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert len(receipts)==34 and sum(r['runtime_audit'] for r in receipts)==1
assert sum(not r['accepted'] and not r['runtime_audit'] for r in receipts)==11
assert sum(r['accepted'] and not r['runtime_audit'] for r in receipts)==22
for r in receipts:
 a=r['attempt'];admit=json.loads((E/f'admission-{a}.json').read_text());turn=json.loads((E/f'turn-{a}.json').read_text())
 assert admit['allowed'] is True and r['source_revision'] and r['source_index_blob']
 assert all(cap in r['command'] for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['swaps']=='0' and turn['exit']==0 and 'STREAMB_SLOTS=3' in turn['command'][-1]
 assert a==47497 if r['runtime_audit'] else (55318<=a<=55350)
 if not r['runtime_audit']:assert r['command'][-1]=='7000'
 if not r['accepted'] and not r['runtime_audit']:
  assert sha(lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sum(q['source_sha256']==r['source_sha256'] for q in receipts)==1
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
allowed_shared={'evidence/pv-lib-20261107/'+x for x in ['PLIB_MAP.json','PLIB_MAP.md','REMAINING.md']}
assert all(p.startswith('lean/PV_LIB_A_') and p.endswith('12.lean') or p.startswith('evidence/pv-lib-20261107/lane-A/') or p in allowed_shared for p in changed)
for p in changed:
 if p.startswith('lean/'):
  assert subprocess.run(['git','cat-file','-e',base+':'+p],capture_output=True).returncode!=0
p=Path('evidence/pv-lib-20261107/PLIB_MAP.json');old=json.loads(subprocess.check_output(['git','show',base+':'+str(p)]));now=json.loads(p.read_text())
assert old['counts']==now['counts'] and len(old['slots'])==len(now['slots'])==170
for before,after in zip(old['slots'],now['slots']):
 assert before=={k:v for k,v in after.items() if k!='session12_prefix_support'}
assert old['lane_A_session11']['deferred']==now['lane_A_session11']['deferred']
assert all(d['status']=='DEFERRED-POST-TARGET' and 'thread-5' in d['reason'] for d in now['lane_A_session11']['deferred'])
# No launcher/runner changes: the authorized553xx guard already existed.
for p in ['evidence/pv-lib-20261107/lane-A/focused-host-s11.py','tools/pv-lib-20261107/run-thread-audit.py']:
 assert Path(p).read_bytes()==subprocess.check_output(['git','show',base+':'+p])
pattern=r'    \(#\[.*?\],\n     #\[.*?\]\)'
old_driver=Path('lean/PV_LIB_A_RawAudit11.lean').read_text();new_driver=Path('lean/PV_LIB_A_RawAudit12.lean').read_text()
assert re.sub(pattern,'ARRAYS',old_driver,count=1,flags=re.S)==re.sub(pattern,'ARRAYS',new_driver,count=1,flags=re.S)
archive=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());compressed=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();raw=lzma.decompress(compressed)
assert sha(compressed)==archive['archive_sha256'] and sha(raw)==archive['uncompressed_sha256']
assert (E/'RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()==sha(raw)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024**2]
subprocess.run(['git','diff','--check'],check=True)
keys=['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256']
(E/'COMPILES.json').write_text(json.dumps([{k:r[k] for k in keys} for r in receipts],indent=2)+'\n')
result=dict(base=base,support_modules=20,strict_roots=90,strict_audit_attempt=47497,
 raw_exit=audit['receipt']['exit'],raw_wall=audit['receipt']['wall'],raw_peak_rss_kbytes=audit['receipt']['peak_rss_kbytes'],raw_swaps=audit['receipt']['swaps'],proof_source_revision=audit['receipt']['source_revision'],
 focused_scopes=33,accepted_focused=22,retained_failed_compiles=[r['attempt'] for r in receipts if not r['accepted'] and not r['runtime_audit']],
 strict_pass=False,original_summary_disagreements=1,offline_constructor_augmented_agreements=90,
 legacy_v2_unchanged=True,historical_slot_statuses_unchanged=True,deferred_post_target_unchanged=True,
 endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,row_closures=0,byte_images_defined=0,
 driver_and_walker_unchanged_except_arrays=True,host_launcher_unchanged=True,all_scopes_capped_and_swap_zero=True,
 next_focused=55351,next_raw=47498,ids_exhausted=False,
 validation='PASS retained-evidence/boundary checks; strict audit EXIT1 preserved and constructor summary reconciled offline; PARTIAL range-to270 and f6-entry-to124 histories; full requested completion NOT achieved; target not established')
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
