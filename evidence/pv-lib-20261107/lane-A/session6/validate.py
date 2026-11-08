"""Validate session6 inputs, receipts, audit and unchanged scope locally."""
import hashlib,json,lzma,pathlib,re,subprocess
A=pathlib.Path('evidence/pv-lib-20261107/lane-A');E=A/'session6'
sha=lambda b:hashlib.sha256(b).hexdigest()
base='9e72b8360546e8e59c25101961856fad85d5c0e9'
receipts=[json.loads(p.read_text())for p in sorted(E.glob('receipt-*.json'))]
assert {r['attempt']for r in receipts}==set(range(47416,47424))|{47491}
accepted={r['target']:r for r in receipts if r['accepted'] and not r['runtime_audit']}
for r in receipts:
 a=r['attempt'];admission=json.loads((E/f'admission-{a}.json').read_text())
 assert admission['allowed'] is True
 assert r['swaps']=='0'
 assert int(r['peak_rss_kbytes'])<8*1024*1024
 cmd=r['command']
 for flag in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert flag in cmd
 assert '7000'in cmd or r['runtime_audit']
 if r['accepted']:
  assert r['exit']=='0'
  assert sha(pathlib.Path(r['source_path']).read_bytes())==r['source_sha256']
 else:
  raw=lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes())
  assert sha(raw)==r['source_sha256']
for e in json.loads((E/'SUPPORT.json').read_text()):
 assert sha(pathlib.Path(e['source']).read_bytes())==e['source_sha256']
 assert accepted[e['module']]['source_sha256']==e['source_sha256']
manifest=json.loads((E/'AUDIT_ROOTS.json').read_text())
audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert audit['strict_raw'] and audit['attempt']==47491 and audit['unresolved']==0 and audit['summary_mismatches']==0
assert {r['root']for r in audit['roots']}==set(manifest['roots'])
assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in audit['roots'])
# Only arrays may differ in the strict driver.
def skeleton(s):return re.sub(r'    \(#\[.*?\],\n     #\[.*?\]\)','ARRAYS',s,count=1,flags=re.S)
assert skeleton(pathlib.Path('lean/PV_LIB_A_RawAudit6.lean').read_text())==skeleton(pathlib.Path('lean/PV_LIB_A_RawAudit5.lean').read_text())
mapfile='evidence/pv-lib-20261107/PLIB_MAP.json'
old=json.loads(subprocess.check_output(['git','show',base+':'+mapfile]))
now=json.loads(pathlib.Path(mapfile).read_text())
assert now['slots']==old['slots'] and now['counts']==old['counts']
for k in old:assert now[k]==old[k]
assert set(now)-set(old)=={'lane_A_session6'}
# Accepted inventory and lane B remain byte-identical to branch head.
inventory=A/'store-write-leaves-v2.json'
assert inventory.read_bytes()==subprocess.check_output(['git','show',base+':'+str(inventory)])
files=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
for p in files:
 assert p.startswith('lean/PV_LIB_A_') or p.startswith(str(A)+'/') or p in [mapfile,'evidence/pv-lib-20261107/REMAINING.md'],p
assert not any(p.stat().st_size>20*1024*1024 for p in E.iterdir()if p.is_file())
summary=dict(base=base,proof_source_revision=audit['receipt']['source_revision'],scope_checked=True,
 slots_unchanged=True,counts=now['counts'],inventory_unchanged=True,driver_walker_unchanged=True,
 focused_attempts=8,accepted_focused=6,failed_focused=[r['attempt']for r in receipts if not r['accepted']],
 source_modules=manifest['modules'],strict_raw_attempt=47491,strict_root_count=len(manifest['roots']),
 raw_exit=audit['receipt']['exit'],raw_wall=audit['receipt']['wall'],raw_peak_rss_kbytes=audit['receipt']['peak_rss_kbytes'],
 raw_swaps=audit['receipt']['swaps'],standard_axioms_only=True,unresolved=0,summary_mismatches=0,
 full_manifest_replayed=False,complete_table=False,complete_D984_adequacy=False,
 caller_histories_completed=False,endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0)
(E/'VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'COMPILES.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(summary,indent=2))
