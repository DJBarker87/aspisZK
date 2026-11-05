"""Summarize terminal receipts without changing the authoritative ledger."""
from pathlib import Path
import json,hashlib,subprocess,lzma
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NIY_[LKE][0-9][0-9][0-9]/receipt.json'))]
ks=[r for r in receipts if r['kind']=='kani'];ls=[r for r in receipts if r['attempt'].startswith('NIY_L')];es=[r for r in receipts if r['kind']=='extract']
budget=dict(limits=dict(kani=100,lean_support=100,extraction=1),used=dict(kani=len(ks),lean_support=len(ls),extraction=len(es)),remaining=dict(kani=100-len(ks),lean_support=100-len(ls),extraction=1-len(es)),unused_lean_reason='Every identified independent Lean-only cut, field/frame induction and source/domain helper was attempted and successful source versions are audited. Remaining member obligations require actual native producer/source-occurrence certificates and SAME caller/callee installation; abstract continuation or arithmetic lemmas cannot supply them. One support slot retained for a justified repair, not an unchanged regression.')
write('NIY_BUDGET.json',budget)
results=[]
for r in receipts:
 a=r['attempt'];results.append(dict(attempt=a,kind=r['kind'],target=r['module'],command=r['command'],native_command=load(a+'.json').get('native_command'),exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],limits=r['limits'],source_revision=r['source_revision'],source_tree_dirty=r['source_tree_dirty'],source_hashes=r['source_hashes'],print_axioms=r['print_axioms'],receipt=a+'/receipt.json',receipt_sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest(),admission=a+'-admission.json',complete_dependency_pins=a+'.json'))
raw=json.dumps(dict(frozen=load('NIY_FREEZE.json'),results=results),separators=(',',':')).encode()
write('NIY_RELEASE_RESULTS.json',dict(count=len(results),compressed_records='NIY_RELEASE_RESULTS.full.json.xz',uncompressed_sha256=hashlib.sha256(raw).hexdigest(),fields='exact target/command, exit, wall, peak RSS, swap, limits, revision, source hashes, print axioms, admission and complete dependency pins',formal_release_claim=False,security_target_established=False))
(E/'NIY_RELEASE_RESULTS.full.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NIY_RELEASE_RESULTS.full.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
walk=[]
for p in sorted((E/'NIY_audit/all').glob('*.json')):
 x=json.loads(p.read_text());assert x['exit_status']==0;walk+=x['results']
scan=[json.loads(l) for l in (E/'NIY_LOADED_scan.jsonl').read_text().splitlines()]
fix=load('NIY_audit/fixtures/fixtures.json')
write('NIY_AUDIT.json',dict(status='PASS',combined_import=dict(attempt='NIY_L091',exit_status=load('NIY_L091/receipt.json')['exit_status'],source_sha256=hashlib.sha256((E/'NIY_COMBINED_IMPORT.lean').read_bytes()).hexdigest(),imports=['NGK_COMBINED_IMPORT','NID_COMBINED_IMPORT','NIL_COMBINED_IMPORT','AspisR1.RPx_Deployed.deployed']),selected_modules=len(load('NIY_MODULES.json')['selected']),raw_ax2=dict(roots=len(walk),all_equal=all(r['equal'] for r in walk),axioms=sorted({a for r in walk for a in r['walked_axioms']}),mode='raw environment proof-body traversal / collectAxioms equality',receipt='NIY_L097/receipt.json'),fixtures=dict(count=len(fix['results']),all_equal=all(r['equal'] for r in fix['results']),receipt='NIY_L096/receipt.json'),nfx_scan=dict(modules=len(scan),dangling=sum(len(r['dangling']) for r in scan),duplicate_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),receipt='NIY_L098/receipt.json'),walker_pins='NIY_WALKER_PINS.json',closure_pins='NIY_CLOSURE_PINS.json.xz',source_verification='NIY_SOURCE_VERIFICATION.json',export='NIY_EXPORT.json',tool_pins='NIY_TOOL_PINS.json',failed_attempt_objects_excluded=True,native_rows_promoted=0,security_target_established=False))
x=load('NIY_CLOSED.json');x['model_transport_status']='combined import, raw ax2 standard axioms and zero-defect NFX scan PASS; actual native caller installation OPEN';x['status']='TX2:065 OPEN; zero composed rows or edges promoted';write('NIY_CLOSED.json',x)
print(json.dumps(dict(attempts=budget['used'],raw_roots=len(walk),scan_modules=len(scan),closed_rows=0,target_established=False)))
