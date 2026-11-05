from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
read=lambda p:json.loads((E/p).read_text())
roots=read('NGT_audit/batch0/proof0.json');fixtures=read('NGT_audit/fixtures/fixtures.json');scan=[json.loads(l) for l in (E/'NGT_LOADED_scan.jsonl').read_text().splitlines()]
standard={'propext','Classical.choice','Quot.sound'}
assert roots['exit_status']==0 and len(roots['results'])==91
assert all(set(r['walked_axioms'])<=standard and r['equal'] for r in roots['results'])
assert fixtures['exit_status']==0 and len(fixtures['results'])==8
for i,r in enumerate(fixtures['results']):assert r['equal'] and (bool(r['walked_axioms']) if i<4 else not r['walked_axioms'])
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
assert read('NGT_L048/receipt.json')['exit_status']==0
attempts=[json.loads(l) for l in (E/'NGT_ATTEMPTS.jsonl').read_text().splitlines()]
summary={k:len([r for r in attempts if r['kind']==k]) for k in ['kani','lean','link','audit','extract']}
x=dict(status='PASS',raw_audit=dict(receipt='NGT_L046/receipt.json',roots=len(roots['results']),standard_axioms=sorted(standard),collectAxioms_agreement=True),fixtures=dict(receipt='NGT_L045/receipt.json',planted=4,mutations=4,all_expected=True),scan=dict(receipt='NGT_L048/receipt.json',modules=len(scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),cached_identical_replicas=sum(len(r['cached_replicas']) for r in scan)),prior_scan=dict(receipt='NGT_L047/receipt.json',exit=1,cause='55 missing import-baseline entries; no dangling/incompatible owner',preserved='NGT_L047_LOADED_scan.jsonl.xz',replacement='NGK pinned baseline plus six pinned source import lists; unchanged stricter scanner'),driver=read('NGT_AUDIT_DRIVER_PINS.json'),attempt_counts_at_audit=summary,resource_limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000),max_rss_kib=max(int(r['peak_rss_kib']) for r in attempts),swaps=sum(int(r['swaps']) for r in attempts),release_replay='cached coherent forest only; not a cold release replay',security_target_established=False)
(E/'NGT_AUDIT.json').write_text(json.dumps(x,indent=1))
(E/'NGT_MODULES.json').write_text(json.dumps([r['module'] for r in scan],indent=1))
print(json.dumps(dict(roots=x['raw_audit']['roots'],scan=x['scan'],summary=summary)))
