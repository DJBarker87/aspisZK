"""Read-only evidence checks; never launches any compiler or audit."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections,re
E=Path(__file__).resolve().parent.relative_to(Path.cwd());A=E.parent;R=A.parent
base='bbb785242b876aa943e9627aa46a7ffa350a860a'
paths=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p.startswith('lean/PV_LIB_A_') or p.startswith(str(A)+'/') or p in {str(R/'PLIB_MAP.json'),str(R/'REMAINING.md')}for p in paths),[p for p in paths if not (p.startswith('lean/PV_LIB_A_') or p.startswith(str(A)+'/') or p in {str(R/'PLIB_MAP.json'),str(R/'REMAINING.md')})]
rs=[json.loads(p.read_text())for p in E.glob('receipt-*.json')];assert len({r['attempt']for r in rs})==len(rs)
assert len(rs)==117 and sum(r['runtime_audit']for r in rs)==1
failed=[]
for r in rs:
 a=r['attempt'];assert (47490<=a<=47499) if r['runtime_audit'] else (46300<=a<=46399 or 47400<=a<=47489)
 assert json.loads((E/f'id-audit-{a}.json').read_text())['hits']==[]
 assert json.loads((E/f'admission-{a}.json').read_text())['allowed'] is True
 assert r['stream_b_turn']['exit']==0
 cmd=r['command'];assert all(x in cmd for x in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert int(r['swaps'])==0 and int(r['peak_rss_kbytes'])<8*1024*1024
 raw=lzma.decompress((E/f'resolution-{a}.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==r['resolution_sha256']
 if not r['accepted']:
  failed.append(a);raw=lzma.decompress((E/f'failed-{a}.lean.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==r['source_sha256']
 else:
  assert r['exit']=='0'
  for line in r.get('axioms_summary_based',[]):assert 'sorryAx'not in line
assert len(failed)==19
roots=json.loads((E/'AUDIT_ROOTS.json').read_text());audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert len(roots['roots'])==len(set(roots['roots']))==118
assert audit['strict_raw'] and audit['unresolved']==audit['summary_mismatches']==0
assert {r['root']for r in audit['roots']}==set(roots['roots'])
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in audit['roots'])
# Verify the strict walker/collector is byte-identical outside the permitted arrays.
a=Path('lean/PV_LIB_RawAudit2.lean').read_text();b=Path('lean/PV_LIB_A_RawAudit5.lean').read_text()
def strip(s):
 start=s.index('  let (modules, roots) :=');end=s.index('  let env ←',start);return s[:start]+s[end:]
assert strip(a)==strip(b)
sup=json.loads((E/'SUPPORT.json').read_text());assert len(sup)==28
for m,s in sup.items():
 assert s['raw_audited'] and s['audit_attempt']==47490
 assert hashlib.sha256(Path(s['source']).read_bytes()).hexdigest()==s['source_sha256']
 assert set(s['roots'])<=set(roots['roots'])
old=json.loads(subprocess.check_output(['git','show',base+':'+str(R/'PLIB_MAP.json')],text=True));new=json.loads((R/'PLIB_MAP.json').read_text())
assert {s['slot']:s['status']for s in old['slots']}=={s['slot']:s['status']for s in new['slots']}
assert old['counts']==new['counts'];assert len(new['slots'])==170
# All unchanged Lane B entries retain their complete content.
assert [s for s in old['slots'] if s['parent'].startswith('slice:')]==[s for s in new['slots'] if s['parent'].startswith('slice:')]
inv=json.loads((A/'store-write-leaves-v2.json').read_text());table=json.loads((E/'STORE_ACTIONS.json').read_text())
assert len(inv['native_boundaries'])==75 and len(inv['all_emitted_thread_native_leaves'])==340
assert {e['id']for e in inv['source_writers']}=={e['function']for e in table['all_inventory_entries']}
assert len(table['new_entries'])==17 and len({e['function']for e in table['new_entries']})==17
assert table['complete_D984_adequacy'] is False
manifest=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());archive=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert hashlib.sha256(archive).hexdigest()==manifest['archive_sha256']
raw=lzma.decompress(archive);assert hashlib.sha256(raw).hexdigest()==manifest['uncompressed_sha256']
summary=dict(base=base,new_modules=28,new_roots=118,focused_pass=97,focused_failed=19,raw_audits=1,raw_attempt=47490,map_slots=170,map_status_changes=0,new_function_projections=17,inventory_candidates=len(inv['source_writers']),complete_D984_adequacy=False,checks='PASS',scope='Evidence/source-cohort integrity, strict audit, write boundaries and unchanged map statuses; not source/machine/binary adequacy')
(E/'VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
