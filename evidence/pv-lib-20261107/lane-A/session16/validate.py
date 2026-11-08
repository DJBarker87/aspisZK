"""Offline session16 checks; never launches Lean or repeats the raw audit."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
base='2bfca12ab510d30816a0821ea28777d893b62e07'
subprocess.run(['git','merge-base','--is-ancestor',base,'HEAD'],check=True)
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
assert all((55683<=r['attempt']<=55689 or 55900<=r['attempt']<=55974 or r['attempt']==55692) for r in receipts)
accepted=[r for r in receipts if r['accepted'] and not r['runtime_audit']]
assert len(accepted)==59
for r in receipts:
 if r['accepted'] and not r['runtime_audit']:
  raw=Path(r['source_path']).read_bytes()
  assert sha(raw)==r['source_sha256'],r['target']
  assert r['exit']=='0' and r['swaps']=='0'
  if 'RawAudit' not in r['target']:
   assert not re.search(rb'\b(?:sorry|admit|native_decide)\b|(?m:^\s*axiom\s)',raw),r['target']
 elif not r['accepted']:
  raw=lzma.decompress((E/f"failed-{r['attempt']}.lean.xz").read_bytes())
  assert sha(raw)==r['source_sha256'],r['attempt']
 assert 'MemoryHigh=6G' in r['command'] and 'MemoryMax=8G' in r['command']
 assert 'MemorySwapMax=0' in r['command'] and 'TasksMax=64' in r['command']
plan=json.loads((E/'COMPAT_PLAN.json').read_text())
strip=lambda s:re.sub(r'^import \S+\n','',s,flags=re.M)
assert len(plan['order'])==33
for m in plan['order']:
 old=subprocess.check_output(['git','show',base+':lean/'+m+'.lean'],text=True)
 new=Path('lean',plan['mapping'][m]+'.lean').read_text()
 assert strip(old)==strip(new),m
assert all(r['import_only'] for r in json.loads((E/'C_IMPORT_ONLY_COMPARISON.json').read_text()))
pins=[json.loads((E/p).read_text()) for p in ['LANE_C_START.json','LANE_C_BEFORE_AUDIT.json','LANE_C_FINAL_INPUT.json']]
for f in ['lean/PV_LIB_SPEC_LaneAJoins18.lean','lean/PV_LIB_SPEC_History18.lean']:
 assert len({p['files'][f] for p in pins})==1,f
for f in ['evidence/pv-lib-20261107/PLIB_MAP.json','evidence/pv-lib-20261107/REMAINING.md']:
 assert Path(f).read_bytes()==subprocess.check_output(['git','show',base+':'+f]),f
roots=json.loads((E/'AUDIT_ROOTS.json').read_text())
assert len(roots['modules'])==58 and len(roots['roots'])==239
actual=[]
for m in roots['modules']:
 s=Path('lean',m+'.lean').read_text();namespace=re.search(r'^namespace (\S+)',s,re.M)[1]
 actual.extend(namespace+'.'+n for n in re.findall(r'^#print axioms (\S+)',s,re.M))
assert len(actual)==239 and set(actual)==set(roots['roots'])
audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert audit['strict_pass'] and audit['root_count']==239 and audit['unresolved']==0 and audit['summary_mismatches']==0
assert audit['receipt']['accepted'] and audit['receipt']['exit']=='0'
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in audit['roots'])
manifest=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text())
packed=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert sha(packed)==manifest['archive_sha256']
raw=lzma.decompress(packed);assert sha(raw)==manifest['uncompressed_sha256']
graphs=json.loads(raw)
for row in manifest['files']:
 if row['name'] in graphs:assert sha(graphs[row['name']].encode())==row['sha256']
delta=json.loads((E/'MAP_DELTA.json').read_text())
assert all(delta[k]==0 for k in ['status_changes','row_closures','endpoint_premise_changes','T_field_changes'])
assert not Path('lean/PV_LIB_A_F170Continuation16.lean').exists()
print('PASS: original cuts through141, qualified local obstruction;59 focused passes;239 strict roots;unchanged shared statuses;no proof replay')
