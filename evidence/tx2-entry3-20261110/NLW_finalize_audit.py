"""Summarize retained scoped results without adding proof or native credit."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
rs=[json.loads(l) for l in (E/'NLW_ATTEMPTS.jsonl').read_text().splitlines()]
std={'propext','Classical.choice','Quot.sound'}
groups=json.loads((E/'NLW_AUDIT_ROOTS.json').read_text())['groups']
proofs=[]
for i,g in enumerate(groups):
 x=json.loads((E/'NLW_audit'/('batch'+str(i))/('proof'+str(i)+'.json')).read_text())
 assert x['exit_status'] in [0,1]
 if x['exit_status']==1:assert any(not r['equal'] for r in x['results'])
 assert {r['root'] for r in x['results']}==set(g)
 for r in x['results']:
  assert set(r['walked_axioms'])<=std,(r['root'],r['walked_axioms'])
  proofs.append(r)
fixtures=json.loads((E/'NLW_audit/fixtures/fixtures.json').read_text())
assert fixtures['exit_status']==0 and len(fixtures['results'])==8
for r in fixtures['results']:
 if r['root'].startswith('NEP_Planted.'):
  assert len(r['walked_axioms'])==1 and r['walked_axioms'][0].startswith('NEP_Planted.')
 else:assert r['walked_axioms']==[]
scan=json.loads((E/'NLW_audit/scan/scan.json').read_text());assert scan['exit_status']==0
rows=[json.loads(l) for l in lzma.decompress((E/'NLW_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in rows)
selectors=json.loads((E/'NLW_SOURCE_SELECTORS.json').read_text())
for m,a in selectors.items():
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()
 r=next(x for x in rs if x['attempt']==a)
 assert r['exit_status']==0 and h in r['source_hashes'].values()
checks=0
for p in E.rglob('*.xz'):
 raw=lzma.decompress(p.read_bytes())
 q=p.with_name(p.name[:-3]+'.sha256')
 if q.exists():assert q.read_text().split()[0]==hashlib.sha256(raw).hexdigest(),p;checks+=1
 if p.parent.name=='NLW_INPUTS':assert p.stem==hashlib.sha256(raw).hexdigest(),p;checks+=1
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not large,large
budget={k:sum(r['kind']==k for r in rs) for k in ['kani','lean','extract']}
assert budget['kani']==40 and budget['lean']<=140 and budget['extract']==0
result=dict(status='SUPPORT_RAW_STANDARD_ONLY_NFX_PASS_WITH_COLLECTOR_FINDING',target='AspisR1.RPx_Deployed.deployed',target_established=False,
 closed_rows=[],proposed_promotions=[],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 source_selectors=selectors,budget=budget,allowance=dict(kani=40,lean=140,extract=0),
 combined_audit_runs=1,focused_import_extensions=1,combined_import_receipt='NLW_L082/receipt.json',
 baseline_module_map='ledger23 receipt NLO_COMBINED_IMPORT.lean resolves as NLS_COMBINED_IMPORT; imported per NLO_HANDOFF/NLS_MODULE_MAP',
 raw_roots=len(proofs),raw_axioms_allowed=sorted(std),raw_nonstandard_axioms=[],
 collector_disagreements=[r for r in proofs if not r['equal']],raw_authoritative_ruling="(ab')(3)/(ax2)",
 retained_nonzero_audit_exits=[r['attempt'] for r in rs if r['kind']=='audit' and r['exit_status']!=0],
 walker=json.loads((E/'NLW_WALKER_PIN.json').read_text()),
 gate_extension=json.loads((E/'NLW_GATE_EXTENSION.json').read_text()),
 nfx=dict(exit_status=0,modules=len(rows),dangling=0,duplicate_owners=0,import_mismatches=0),
 fixture_controls=fixtures['results'],compressed_hash_checks=checks,
 metrics=dict(scopes=len(rs),max_peak_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in rs),
  swap_values=sorted({str(r['swaps']) for r in rs}),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),
  total_wall_seconds=sum(float(r['wall_seconds']) for r in rs)),
 kani_summary=dict(exit0=sum(r['kind']=='kani' and r['exit_status']==0 for r in rs),
  timeout=['NLW_K039'],compile_rejection=['NLW_K001'],pairs='NLW_NATIVE_PAIRS.json',credit='SUPPORT ONLY'),
 lean_summary=dict(exit0=sum(r['kind']=='lean' and r['exit_status']==0 for r in rs),
  failed_attempts=[r['attempt'] for r in rs if r['kind']=='lean' and r['exit_status']!=0],current_sources='43 individually compiled modules; import extension and gate modules'),
 trust_rows_added=[],trust_rows_removed=[],pending_runtime_rows_used=[],
 frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool_source='b936275465',
 elf_status='Inherited pins only; no shipped source changes or ELF rebuild/remeasurement. Default f8c0ec72…,devnet63ad3e9c…,Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',
 incomplete=['actual parent/frame/call-boundary native producers','full233/242 native resource packets','caller root provenance/collision event installation','next ledger gate'])
(E/'NLW_AUDIT.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(status=result['status'],budget=budget,roots=len(proofs),modules=len(rows),compressed_hash_checks=checks)))
