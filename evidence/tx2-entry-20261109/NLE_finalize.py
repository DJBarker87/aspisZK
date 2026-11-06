from pathlib import Path
import json,hashlib,lzma,subprocess,re
E=Path(__file__).resolve().parent
modules=json.loads((E/'NLE_MODULES.json').read_text())+['NLE_COMBINED_IMPORT']
receipts=[json.loads(p.read_text()) for p in E.glob('NLE_[LK]*/receipt.json')]
selected={}
for module in modules:
 h=hashlib.sha256((E/(module+'.lean')).read_bytes()).hexdigest()
 candidates=[r for r in receipts if r['kind']=='lean' and r['module']==module and r['exit_status']==0 and h in r['source_hashes'].values()]
 assert candidates,('No successful final source',module)
 selected[module]=sorted(candidates,key=lambda r:r['attempt'])[-1]['attempt']
roots=json.loads((E/'NLE_AUDIT_ROOTS.json').read_text())['roots'];walks=[]
for p in (E/'NLE_audit').rglob('proof*.json'):
 row=json.loads(p.read_text());assert row['exit_status']==0
 for result in row['results']:
  assert result['equal'] and result['collect_axioms']==result['walked_axioms'],result
  assert set(result['walked_axioms']) <= {'propext','Classical.choice','Quot.sound'},result
  walks.append(result)
assert sorted(r['root'] for r in walks)==sorted(roots)
scanfile=E/'NLE_LOADED_scan.jsonl'
raw=scanfile.read_bytes() if scanfile.exists() else lzma.decompress(scanfile.with_name(scanfile.name+'.xz').read_bytes())
scan=[json.loads(line) for line in raw.decode().splitlines() if line.strip()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
fixtures=json.loads((E/'NLE_audit/fixtures/fixtures.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8 and all(r['equal'] for r in fixtures['results'])
lean=[r for r in receipts if r['kind']=='lean'];native=[r for r in receipts if r['kind']=='kani']
started=[]
for r in native:
 p=E/(r['attempt']+'-graph-check.json')
 if p.exists() and json.loads(p.read_text()).get('graph_matches_frozen') and (E/(r['attempt']+'-lock-check.json')).exists():started.append(r['attempt'])
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 assert str(r['swaps'])=='0'
report=dict(status='SOURCE_SUPPORT_AUDIT_PASS_NOT_COMPLETE_PARAMETERIZED_FOLDS',target='AspisR1.RPx_Deployed.deployed',target_established=False,closed_rows=[],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,source_selectors=selected,budget=dict(allowance=dict(kani=30,lean=130,extraction=0),actual_lean_compiler_invocations=len(lean),capped_native_receipts=len(native),actual_cargo_kani_invocations=len(started),native_attempts=started,extraction=0),combined_source_sets=1,scanner_runs=2,scanner_first_failure='Expected-import generator omitted implicit Init for34 new modules; corrected own inputs, validation unchanged',scan=dict(modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),raw_axioms=dict(roots=len(walks),standard_only=True,reused_roots=0),fixtures=dict(count=8,passed=True),missing_interfaces='NLE_CHILD_INTERFACE_FINDING.json',native_scope='NLE_CUTS.md; unsafe diagnostics excluded; safe segments metadata/Result only',remaining='NLE_REMAINING.md',limits='6G high /8G max /swap0 /tasks64; Lean -M7000; no raised timeout/cap')
(E/'NLE_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>20_000_000:
  assert p.suffix!='.xz',('Oversized archive',p)
  data=p.read_bytes();p.with_name(p.name+'.xz').write_bytes(lzma.compress(data,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n');p.unlink()
print(json.dumps(dict(source_modules=len(modules),roots=len(walks),scanner_modules=len(scan),lean=len(lean),native=len(started),closed=0)))
