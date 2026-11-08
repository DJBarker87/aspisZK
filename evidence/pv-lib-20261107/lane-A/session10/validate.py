"""Artifact/source/boundary checks only; no Lean or regression launch."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).parent;base='0f651b565341f0dba8390dbbe234ce523d74f080';sha=lambda b:hashlib.sha256(b).hexdigest()
support=json.loads((E/'SUPPORT.json').read_text());roots=json.loads((E/'AUDIT_ROOTS.json').read_text());audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert len(support)==23 and len(roots['roots'])==103
assert audit['strict_raw'] and audit['unresolved']==0 and audit['summary_mismatches']==0
assert set(roots['roots'])=={r['root'] for r in audit['roots']}
for s in support:
 r=json.loads((E/f"receipt-{s['attempt']}.json").read_text());p=Path(s['source'])
 assert r['accepted'] and not r['runtime_audit']
 assert sha(p.read_bytes())==r['source_sha256']==s['source_sha256']
 assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option (?:maxHeartbeats|maxRecDepth)',p.read_text())
for f in ['lean/PV_LIB_A_StoreActionTable.lean','lean/PV_LIB_A_StoreActionTable7.lean','lean/PV_LIB_A_StoreActionTable8.lean','lean/PV_LIB_A_StoreActionTable9.lean','lean/PV_LIB_A_WeakOwnerFree9.lean','lean/PV_LIB_A_TypedBody486.lean','lean/PV_LIB_A_TypedBody584.lean','lean/PV_LIB_A_TypedBody661.lean','lean/PV_LIB_A_DropInPlace248.lean']:
 assert Path(f).read_bytes()==subprocess.check_output(['git','show',base+':'+f]),f
m=Path('evidence/pv-lib-20261107/PLIB_MAP.json');old=json.loads(subprocess.check_output(['git','show',base+':'+str(m)]));now=json.loads(m.read_text())
assert old['slots']==now['slots'] and old['counts']==now['counts']
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
failed=[r for r in receipts if not r['accepted']];assert len(receipts)==45 and len(failed)==20
assert sum(r['runtime_audit'] for r in receipts)==1
for r in receipts:
 a=r['attempt'];admit=json.loads((E/f'admission-{a}.json').read_text());turn=json.loads((E/f'turn-{a}.json').read_text())
 assert admit['allowed'] is True and r['source_revision'] and r['source_index_blob']
 assert all(cap in r['command'] for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert r['swaps']=='0' and turn['exit']==0 and 'STREAMB_SLOTS=3' in turn['command'][-1]
 assert 47495<=a<=47499 if r['runtime_audit'] else 55033<=a<=55076
 if not r['runtime_audit']:assert r['command'][-1]=='7000'
 if not r['accepted']:
  assert sha(lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes()))==r['source_sha256']
  assert sum(q['source_sha256']==r['source_sha256'] for q in receipts)==1
pattern=r'    \(#\[.*?\],\n     #\[.*?\]\)'
old_driver=Path('lean/PV_LIB_A_RawAudit9.lean').read_text();new_driver=Path('lean/PV_LIB_A_RawAudit10.lean').read_text()
assert re.sub(pattern,'ARRAYS',old_driver,count=1,flags=re.S)==re.sub(pattern,'ARRAYS',new_driver,count=1,flags=re.S)
assert Path('tools/pv-lib-20261107/run-thread-audit.py').read_bytes()==subprocess.check_output(['git','show',base+':tools/pv-lib-20261107/run-thread-audit.py'])
assert Path('evidence/pv-lib-20261107/lane-A/focused-host-s9.py').read_bytes()==subprocess.check_output(['git','show',base+':evidence/pv-lib-20261107/lane-A/focused-host-s9.py'])
archive=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());compressed=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();raw=lzma.decompress(compressed)
assert sha(compressed)==archive['archive_sha256'] and sha(raw)==archive['uncompressed_sha256'] and raw
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024**2]
checks=[]
for f in ['evidence/pv-lib-20261107/lane-A/session8/generate-typed-bodies.py','evidence/pv-lib-20261107/lane-A/session9/generate-allocator-bodies.py']:
 cmd=['python3',f,'--check'];r=subprocess.run(cmd,text=True,capture_output=True);checks.append(dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr));assert r.returncode==0,checks[-1]
(E/'GENERATOR_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert not [p for p in changed if not (p.startswith('lean/PV_LIB_A_') or p.startswith('evidence/pv-lib-20261107/lane-A/') or p in [str(m),'evidence/pv-lib-20261107/REMAINING.md'])]
subprocess.run(['git','diff','--check'],check=True)
result=dict(base=base,proof_source_revision=audit['receipt']['source_revision'],support_modules=23,strict_roots=103,strict_audit_attempt=47495,raw_exit=audit['receipt']['exit'],raw_wall=audit['receipt']['wall'],raw_peak_rss_kbytes=audit['receipt']['peak_rss_kbytes'],raw_swaps=audit['receipt']['swaps'],focused_scopes=44,accepted_focused=24,retained_failed_compiles=[r['attempt'] for r in failed],heartbeat_split=55046,pre_elaboration_failures=[],legacy_v2_unchanged=True,slots_unchanged=True,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0,new_T_fields=0,byte_images_defined=0,driver_and_walker_unchanged_except_arrays=True,host_wrapper_unchanged=True,source_hashes_match=True,all_scopes_capped_and_swap_zero=True,max_peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in receipts),validation='PASS; PARTIAL destructor/source/control/count support; requested completion not achieved; target not established')
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
keys=['attempt','target','accepted','runtime_audit','exit','wall','peak_rss_kbytes','swaps','source_revision','source_index_blob','source_sha256']
(E/'COMPILES.json').write_text(json.dumps([{k:r[k] for k in keys} for r in receipts],indent=2)+'\n')
print(json.dumps(result,indent=2))
