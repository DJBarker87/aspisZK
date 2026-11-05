from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[read(p) for p in sorted(E.glob('NIL_[KLE][0-9][0-9][0-9]/receipt.json'))]
fields=['attempt','kind','module','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits']
(E/'NIL_RELEASE_RESULTS.json').write_text(json.dumps([{k:r[k] for k in fields} for r in receipts],indent=1)+'\n')
roots=[];groups=read(E/'NIL_AUDIT_ROOTS.json')['groups']
for i in range(len(groups)):
 x=read(E/f'NIL_audit/batch{i}/proof{i}.json');assert x['exit_status']==0;roots+=x['results']
expected={n for g in groups for n in g};assert {r['root'] for r in roots}==expected
for r in roots:assert r['equal'] is True and set(r['walked_axioms'])==set(r['collect_axioms']) and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
fixture=read(E/'NIL_audit/fixtures/fixtures.json');assert fixture['exit_status']==0 and len(fixture['results'])==8
pins=[read(E/f'NIL_L{i:03}/NIL_ProofDriver_BINARY_PIN.json') for i in range(64,70)];assert all(p==pins[0] for p in pins)
scan=[json.loads(l) for l in (E/'NIL_LOADED_scan.jsonl').read_text().splitlines()];assert read(E/'NIL_audit/scan/scan.json')['exit_status']==0
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
scanner=dict(status='PASS',exit_status=0,modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0)
provenance=read(E/'NIL_AUDIT_DRIVER_PROVENANCE.json');assert provenance['walker_byte_identical']
audit=dict(status='PASS',roots=roots,root_count=len(roots),standard_axioms=sorted({a for r in roots for a in r['walked_axioms']}),walker_byte_identical=True,walker_source_sha256=provenance['walker_source_sha256'],driver_source_sha256=sha(E/'NIL_ProofDriver.lean'),driver_binary_pin=pins[0],fixtures=dict(exit_status=0,results=8,same_binary=True),scanner=scanner,combined_import='NIL_L060',statement_audit='NIL_L061',selected_modules=read(E/'NIL_MODULES.json'),excluded_failed_candidates=['NIL_SourceModel','NIL_TailPort'],release_scope='focused coherent cached replay; zero composed-row promotions; no cold frozen manifest replay')
(E/'NIL_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n');(E/'NIL_SCAN.json').write_text(json.dumps(scanner,indent=2)+'\n')
counts=dict(kani=sum(r['kind']=='kani' for r in receipts),extract=sum(r['kind']=='extract' for r in receipts));counts['lean_support']=len(receipts)-counts['kani']-counts['extract']
assert counts['kani']<=120 and counts['extract']<=1 and counts['lean_support']<=80
budget=dict(used=counts,maximum=dict(kani=120,extract=1,lean_support=80),wall_seconds=sum(float(r['wall_seconds']) for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),remaining='See NIL_REMAINING.md; no unresolved local result promoted.')
(E/'NIL_BUDGET.json').write_text(json.dumps(budget,indent=2)+'\n');print(json.dumps(dict(audit_roots=len(roots),scanner=scanner,budget=budget)))
