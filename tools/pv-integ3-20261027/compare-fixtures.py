"""Fixed-coin byte/record comparison; retain elapsed-time metadata separately."""
from pathlib import Path
import json,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298')
B=H/'baseline/fixtures-candidate';rows=[]
sha=lambda b:hashlib.sha256(b).hexdigest()
for fixture in ['transfer','withdrawal']:
 paths={'baseline':B/(fixture+'-0'),'candidate':H/'fixtures-candidate'/(fixture+'-0')};files={};records={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()}
 for name in ['public.bin','proof.bin']:
  bs={k:(p/name).read_bytes() for k,p in paths.items()}
  files[name]=dict(byte_identical=bs['baseline']==bs['candidate'],**{k:dict(sha256=sha(b),bytes=len(b)) for k,b in bs.items()})
 ledgers={k:{str(p.relative_to(v/'ledger')):p.read_bytes() for p in (v/'ledger').rglob('*') if p.is_file()} for k,v in paths.items()}
 deterministic={k:json.dumps({f:x for f,x in v.items() if f!='seconds'},sort_keys=True,separators=(',',':')).encode() for k,v in records.items()}
 raw={k:(v/'result.json').read_bytes() for k,v in paths.items()}
 row=dict(fixture=fixture,files=files,deterministic_result_records_byte_identical=deterministic['baseline']==deterministic['candidate'],deterministic_records={k:dict(sha256=sha(b),bytes=len(b),canonical_json=b.decode()) for k,b in deterministic.items()},raw_result_json_byte_identical=raw['baseline']==raw['candidate'],raw_result_json={k:dict(sha256=sha(b),bytes=len(b)) for k,b in raw.items()},raw_result_differing_fields=[f for f in set(records['baseline'])|set(records['candidate']) if records['baseline'].get(f)!=records['candidate'].get(f)],records=records,ledger_files_byte_identical=ledgers['baseline']==ledgers['candidate'],ledger_manifest={k:{p:dict(sha256=sha(b),bytes=len(b)) for p,b in v.items()} for k,v in ledgers.items()})
 rows.append(row)
r=dict(baseline_revision='37e5e133f89f4aa5909a1ca6fc81237d2c977947',baseline_build_revision=(H/'baseline/source-revision.txt').read_text().strip(),candidate_revision=(H/'source-revision.txt').read_text().strip(),coin=0,comparisons=rows,elapsed_time_metadata_excluded=['seconds'],passed=all(all(x['byte_identical'] for x in r['files'].values()) and r['deterministic_result_records_byte_identical'] and r['ledger_files_byte_identical'] for r in rows),literal_raw_result_json_passed=all(r['raw_result_json_byte_identical'] for r in rows))
(H/'fixture-comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));sys.exit(0 if r['passed'] else 2)
