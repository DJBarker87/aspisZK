from pathlib import Path
import json,re,hashlib,collections
from NGU_io import raw,text,read,E
attempts=[json.loads(l) for l in text(E/'NGU_ATTEMPTS.jsonl').splitlines()]
rawroots=[];nested=[]
for i in range(26):
 r=read(E/f'NGU_audit/batch{i}/proof{i}.json');assert r['exit_status']==0;rawroots+=r['results'];nested.append(r)
A=read(E/'NGU_AUDIT_ROOTS.json');expected=[n for g in A['groups'] for n in g]
assert collections.Counter(x['root'] for x in rawroots)==collections.Counter(expected)
standard={'propext','Classical.choice','Quot.sound'}
assert all(set(x['walked_axioms'])<=standard and x['equal'] for x in rawroots)
fixtures=read(E/'NGU_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8
assert all(r['equal'] for r in fixtures['results'])
assert all(r['walked_axioms'] for r in fixtures['results'][:4]) and all(not r['walked_axioms'] for r in fixtures['results'][4:])
scan=[json.loads(l) for l in text(E/'NGU_LOADED_scan.jsonl').splitlines()]
S=dict(modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan))
assert not any(S[k] for k in ['dangling','incompatible_owners','import_mismatches'])
(E/'NGU_SCAN.json').write_text(json.dumps(S,indent=1)+'\n')
statements=[]
for r in attempts:
 if r['kind']=='lean' and r['module'].startswith('NGU_Statements') and r['exit_status']==0:
  for line in text(E/r['attempt']/'stdout.log').splitlines():
   if line.startswith('NGU_CERT_ENTRY '):statements.append(json.loads(line[len('NGU_CERT_ENTRY '):]))
assert collections.Counter(r['name'] for r in statements)==collections.Counter(A['roots'])
owners=read(E/'NGU_STATEMENT_ROOTS.json')['owners'];assert all(r['owner']==owners[r['name']] for r in statements)
(E/'NGU_CERT_ASSOCIATIONS.json').write_text(json.dumps(statements,indent=1)+'\n')
# Verify the actual walker source is the hardened original, before claiming ax2.
import subprocess
original=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'])
actual=subprocess.check_output(['git','show','HEAD:evidence/slice-d-prepared-20261105/NGN_WALKER_SOURCE.lean.txt'])
assert actual==original
(E/'NGU_WALKER_CONFORMANCE.json').write_text(json.dumps(dict(source='evidence/slice-d-prepared-20261105/NGN_WALKER_SOURCE.lean.txt',hardened_original='evidence/axaudit2-20261102/NEP_WALKER.lean',byte_identical=True,sha256=hashlib.sha256(actual).hexdigest(),fixture_binary=read(E/'NGU_L040/NGU_ProofDriver_BINARY_PIN.json'),driver_changes='NGN -> NGU selection/runtime filenames only; full diffs committed'),indent=1)+'\n')
counts=collections.Counter(r['kind'] for r in attempts)
report=dict(root='AspisR1.NGU_PreparedClaim.packet',headline='AspisR1.RPx_Deployed.deployed',canonical_model='CHECKED',hybrid_native_association='OPEN; NGU_HYBRID_GAPS.md',composed_status='OPEN',raw_axiom_roots=len(rawroots),raw_standard_only=True,collect_axioms_disagreements=sum(not r['equal'] for r in rawroots),fixtures=fixtures,scan=S,checked_statement_owners=len(statements),allocations=dict(counts),lean_support_allocations=sum(v for k,v in counts.items() if k not in ['kani','extract']),kani_allocations=counts['kani'],extraction_runs=counts.get('extract',0),successful_allocations=sum(r['exit_status']==0 for r in attempts),wall_sum_seconds=sum(r['wall_seconds'] for r in attempts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in attempts),swap_sum=sum(int(r['swaps']) for r in attempts),source_revisions='Raw receipts/configurations plus NGU_REVISION_ASSOCIATION.json for early missing metadata',per_target_section6='NGU_ATTEMPTS.jsonl and exact full_receipt paths; nested raw audit receipts retain full axioms lines',cold_release_replay=False,new_closed_rows=[],security_target_established=False)
(E/'NGU_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps({k:report[k] for k in ['raw_axiom_roots','checked_statement_owners','allocations','lean_support_allocations','kani_allocations','wall_sum_seconds','peak_rss_kib','swap_sum']}))
