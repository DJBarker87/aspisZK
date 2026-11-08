"""Validate exact sources, receipts, scope and the single final strict audit."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
A=Path('evidence/pv-lib-20261107/lane-A');E=A/'session7';base='03c3c72b1436a3cd5677265b0682a9490a4f4878'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text())for p in sorted(E.glob('receipt-*.json'))]
expected=set(range(47424,47451))-{47445}|{47492}
assert {r['attempt']for r in receipts}==expected
for r in receipts:
 a=r['attempt'];assert json.loads((E/f'admission-{a}.json').read_text())['allowed']is True
 assert r['swaps']=='0'and int(r['peak_rss_kbytes'])<8*1024*1024
 for flag in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert flag in r['command']
 assert '7000'in r['command']or r['runtime_audit']
 raw=Path(r['source_path']).read_bytes()if r['accepted']else lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes())
 assert sha(raw)==r['source_sha256']
 assert sha(subprocess.check_output(['git','show',r['source_index_blob']]))==r['source_sha256']
 if r['accepted']:assert r['exit']=='0'and not any('sorryAx'in v for v in r['axioms_summary_based'])
refused=json.loads((E/'refusal-47445.json').read_text());assert not refused['compiler_started']
assert json.loads((E/'admission-47445.json').read_text())['allowed']is False
assert len([r for r in receipts if r['runtime_audit']])==1
support=json.loads((E/'SUPPORT.json').read_text());manifest=json.loads((E/'AUDIT_ROOTS.json').read_text());audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert audit['strict_raw']and audit['attempt']==47492 and audit['unresolved']==0 and audit['summary_mismatches']==0
assert {r['root']for r in audit['roots']}==set(manifest['roots'])
assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in audit['roots'])
for r in support:assert sha(Path(r['source']).read_bytes())==r['source_sha256']
def skeleton(s):return re.sub(r'    \(#\[.*?\],\n     #\[.*?\]\)','ARRAYS',s,count=1,flags=re.S)
assert skeleton(Path('lean/PV_LIB_A_RawAudit7.lean').read_text())==skeleton(Path('lean/PV_LIB_A_RawAudit6.lean').read_text())
for p in ['lean/PV_LIB_A_StoreActionTable.lean','lean/PV_LIB_A_StoreActionMachine.lean',str(A/'store-write-leaves-v2.json'),str(A/'store-write-leaves-v2.md')]:
 assert Path(p).read_bytes()==subprocess.check_output(['git','show',base+':'+p])
mp='evidence/pv-lib-20261107/PLIB_MAP.json';old=json.loads(subprocess.check_output(['git','show',base+':'+mp]));now=json.loads(Path(mp).read_text())
assert all(now[k]==v for k,v in old.items())and set(now)-set(old)=={'lane_A_session7'}
assert len(now['slots'])==170
for p in subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines():
 assert p.startswith('lean/PV_LIB_A_')or p.startswith(str(A)+'/')or p in [mp,'evidence/pv-lib-20261107/REMAINING.md'],p
assert all(p.stat().st_size<=20*1024*1024 for p in E.rglob('*')if p.is_file())
(E/'COMPILES.json').write_text(json.dumps(receipts,indent=2)+'\n')
summary=dict(base=base,proof_source_revision=audit['receipt']['source_revision'],scope_checked=True,inventory_unchanged=True,legacy_v2_unchanged=True,slot_records_unchanged=True,counts=now['counts'],failed_focused=[r['attempt']for r in receipts if not r['accepted']],admission_refusals=[47445],focused_receipts=len(receipts)-1,accepted_focused=sum(r['accepted']and not r['runtime_audit']for r in receipts),support_modules=len(support),strict_raw_attempt=47492,strict_root_count=len(manifest['roots']),raw_exit=audit['receipt']['exit'],raw_wall=audit['receipt']['wall'],raw_peak_rss_kbytes=audit['receipt']['peak_rss_kbytes'],raw_swaps=audit['receipt']['swaps'],standard_axioms_only=True,unresolved=0,summary_mismatches=0,driver_walker_unchanged=True,full_manifest_replayed=False,complete_table=False,complete_D984_adequacy=False,caller_histories_completed=False,endpoint_premises_removed=0,endpoint_premises_added=0,new_T_fields=0)
(E/'VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
