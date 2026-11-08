"""Offline retained-evidence/source/boundary validation; launches no builds."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).parent
base='280cd5669b0fb283ea4ba6ffd364db2c9de2d1e4'
sha=lambda b:hashlib.sha256(b).hexdigest()
support=json.loads((E/'SUPPORT.json').read_text());manifest=json.loads((E/'AUDIT_ROOTS.json').read_text());audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert len(support)==16 and len(manifest['roots'])==77
assert audit['strict_raw'] and audit['unresolved']==audit['summary_mismatches']==0
assert set(manifest['roots'])=={r['root'] for r in audit['roots']}
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in audit['roots'])
for s in support:
 r=json.loads((E/f"receipt-{s['attempt']}.json").read_text());p=Path(s['source'])
 assert r['accepted'] and sha(p.read_bytes())==r['source_sha256']==s['source_sha256']
 assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option (?:maxHeartbeats|maxRecDepth)',p.read_text())
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert len(receipts)==32 and sum(r['runtime_audit'] for r in receipts)==1
assert sum(not r['accepted'] for r in receipts)==14
assert sum(r['accepted'] and not r['runtime_audit'] for r in receipts)==17
for r in receipts:
 a=r['attempt'];admit=json.loads((E/f'admission-{a}.json').read_text());turn=json.loads((E/f'turn-{a}.json').read_text())
 assert admit['allowed'] is True and r['source_revision'] and r['source_index_blob']
 assert all(cap in r['command'] for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['swaps']=='0' and turn['exit']==0 and 'STREAMB_SLOTS=3' in turn['command'][-1]
 assert (47496<=a<=47499 or 55090<=a<=55099 or 55390<=a<=55399) if r['runtime_audit'] else (55077<=a<=55089 or 55300<=a<=55389)
 if not r['runtime_audit']:assert r['command'][-1]=='7000'
 if not r['accepted']:
  assert sha(lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sum(q['source_sha256']==r['source_sha256'] for q in receipts)==1
# Existing proved modules, old runtime APIs and every provider/implementation remain unchanged.
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
allowed_shared={'evidence/pv-lib-20261107/'+x for x in ['PLIB_MAP.json','PLIB_MAP.md','REMAINING.md']}
assert all(p.startswith('lean/PV_LIB_A_') and p.endswith('11.lean') or p.startswith('evidence/pv-lib-20261107/lane-A/') or p in allowed_shared for p in changed)
for p in changed:
 if p.startswith('lean/'):
  assert subprocess.run(['git','cat-file','-e',base+':'+p],capture_output=True).returncode!=0
m=Path('evidence/pv-lib-20261107/PLIB_MAP.json');old=json.loads(subprocess.check_output(['git','show',base+':'+str(m)]));now=json.loads(m.read_text())
assert old['counts']==now['counts'] and len(old['slots'])==len(now['slots'])==170
for before,after in zip(old['slots'],now['slots']):
 assert before=={k:v for k,v in after.items() if k not in ['session11_scope','session11_prefix_support']}
assert all(d['status']=='DEFERRED-POST-TARGET' and 'thread-5' in d['reason'] for d in now['lane_A_session11']['deferred'])
# The private launcher changed ONLY the authorized553xx guards.
b=E.parent
oldhost=(b/'focused-host-s9.py').read_text();host=(b/'focused-host-s11.py').read_text()
assert host==oldhost.replace('or 55000<=a<=55089','or 55000<=a<=55089 or 55300<=a<=55389').replace('or 55090<=a<=55099','or 55090<=a<=55099 or 55390<=a<=55399')
pattern=r'    \(#\[.*?\],\n     #\[.*?\]\)'
old_driver=Path('lean/PV_LIB_A_RawAudit10.lean').read_text();new_driver=Path('lean/PV_LIB_A_RawAudit11.lean').read_text()
assert re.sub(pattern,'ARRAYS',old_driver,count=1,flags=re.S)==re.sub(pattern,'ARRAYS',new_driver,count=1,flags=re.S)
p=Path('tools/pv-lib-20261107/run-thread-audit.py');assert p.read_bytes()==subprocess.check_output(['git','show',base+':'+str(p)])
archive=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());compressed=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();raw=lzma.decompress(compressed)
assert sha(compressed)==archive['archive_sha256'] and sha(raw)==archive['uncompressed_sha256']
assert (E/'RAW_GRAPH_ARCHIVE.json.sha256').read_text().strip()==sha(raw)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024**2]
subprocess.run(['git','diff','--check'],check=True)
keys=['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256']
(E/'COMPILES.json').write_text(json.dumps([{k:r[k] for k in keys} for r in receipts],indent=2)+'\n')
result=dict(base=base,support_modules=16,strict_roots=77,strict_audit_attempt=47496,
 raw_exit=audit['receipt']['exit'],raw_wall=audit['receipt']['wall'],raw_peak_rss_kbytes=audit['receipt']['peak_rss_kbytes'],raw_swaps=audit['receipt']['swaps'],proof_source_revision=audit['receipt']['source_revision'],
 focused_scopes=31,accepted_focused=17,retained_failed_compiles=[r['attempt'] for r in receipts if not r['accepted']],heartbeat_split=55308,
 legacy_v2_unchanged=True,historical_slot_statuses_unchanged=True,scope_dispositions='DEFERRED-POST-TARGET per D999/thread-5',
 endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,row_closures=0,byte_images_defined=0,
 driver_and_walker_unchanged_except_arrays=True,host_wrapper_change='authorized553xx guards only',all_scopes_capped_and_swap_zero=True,
 next_focused=55318,next_raw=47497,ids_exhausted=False,
 validation='PASS; PARTIAL actual range and early f6 histories only; full requested completion not achieved; target not established')
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
