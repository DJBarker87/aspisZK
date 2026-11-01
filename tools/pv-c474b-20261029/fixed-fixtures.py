"""Exact Cargo unit graphs (no compilation) and the existing fixed-coin fixture gate."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');R=H/'src'
sha=lambda b:hashlib.sha256(b).hexdigest()
# Same two successful fixtures, same coin 0, existing D328 deterministic criterion.
subprocess.run([H/'native-target/client/pv-c474-fixture',H/'bundle/fixed-fixtures','0','1'],check=True)
G=Path('/home/dombarker/project-offloads/codex-pv-gate6-20261028');pins=json.loads((G/'fixture-control-pins.json').read_text());rows=[]
B=Path('/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298/baseline/fixtures-candidate')
for f in ['transfer','withdrawal']:
 a=B/(f+'-0');b=H/'bundle/fixed-fixtures'/(f+'-0');expected=pins[f]
 files={}
 for name,pin in expected['files'].items():
  av=(a/name).read_bytes();bv=(b/name).read_bytes();assert sha(av)==pin['sha256'] and len(av)==pin['bytes']
  files[name]=dict(identical=av==bv,baseline_sha256=sha(av),draft_sha256=sha(bv),bytes=len(bv))
 assert sha((a/'result.json').read_bytes())==expected['raw_result_json']['sha256']
 records={k:json.loads((p/'result.json').read_text()) for k,p in [('baseline',a),('draft',b)]}
 canonical={k:json.dumps({x:y for x,y in v.items() if x!='seconds'},sort_keys=True,separators=(',',':')) for k,v in records.items()}
 ledgers={k:{str(p.relative_to(v/'ledger')):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in (v/'ledger').rglob('*') if p.is_file()} for k,v in [('baseline',a),('draft',b)]}
 assert ledgers['baseline']==expected['ledger_manifest']
 row=dict(fixture=f,files=files,canonical_records_identical=canonical['baseline']==canonical['draft'],canonical_records=canonical,ledger_identical=ledgers['baseline']==ledgers['draft'],ledger_manifest=ledgers)
 assert all(x['identical'] for x in files.values()) and row['canonical_records_identical'] and row['ledger_identical'],row
 rows.append(row)
(H/'bundle/fixed-fixture-comparison.json').write_text(json.dumps(dict(passed=True,coin=0,comparisons=rows,control_pins=pins,scope='Existing D328 deterministic fixed-coin gate, candidate rerun; retained golden control verified read-only, no unchanged control proof regeneration'),indent=2)+'\n');print('FIXED_FIXTURES_PASS',flush=True)
