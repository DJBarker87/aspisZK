"""Summarize actual receipts; never infer row credit from support passes."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
receipts=[read(p) for p in E.glob('NLI_[LK][0-9][0-9][0-9]/receipt.json')]
mods=read(E/'NLI_MODULES.json');required=set(read(E/'NLI_AUDIT_ROOTS.json')['roots'])
proofs=[read(p)for p in (E/'NLI_audit').glob('proof*/proof*.json')]
results=[r for p in proofs for r in p['results']]
observed=[r['root']for r in results];standard={'propext','Classical.choice','Quot.sound'}
nonstandard=[r for r in results if set(r['walked_axioms'])-standard]
disagreements=[r for r in results if not r['equal']]
scan=[json.loads(l)for l in(E/'NLI_LOADED_scan.jsonl').read_text().splitlines()]
fixtures=read(E/'NLI_audit/fixtures/fixtures.json')['results']
combined=[r for r in receipts if r.get('module')=='NLI_COMBINED_IMPORT'and r['kind']=='lean']
scans=[r for r in receipts if r.get('command')==['python3','NLI_audit_batch.py','scan']]
comparison=read(E/'NLI_PREDECESSOR_COMPARISON.json')
a=dict(status='VALIDATED SUPPORT ONLY; target not yet established',headline='AspisR1.RPx_Deployed.deployed',row_delta=0,row_roots=[],parameterized_native_folds=[],source_goal_proved='AspisR1.NLI_Source.finishSourceEquality',full_combined_audits=len(combined),combined=[{k:r[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}for r in combined],scan_attempt=scans[-1]['attempt'],scan_exit=scans[-1]['exit_status'],modules=len(scan),dangling=sum(len(x['dangling'])for x in scan),conflicting_owners=sum(len(x['duplicate_owners'])for x in scan),import_mismatches=sum(not x['imports_match']for x in scan),compatible_cached_replicas=sum(len(x['cached_replicas'])for x in scan),required_raw_roots=len(required),raw_result_count=len(results),missing_raw_roots=sorted(required-set(observed)),unexpected_raw_roots=sorted(set(observed)-required),duplicate_raw_roots=len(observed)-len(set(observed)),raw_standard_axioms_only=not nonstandard,nonstandard_axioms=nonstandard,collect_axioms_disagreements=disagreements,raw_authority='(ab\')(3)/(ax2)',fixtures=fixtures,predecessor_comparison=comparison,budgets=dict(kani_used=sum(r['kind']=='kani'for r in receipts),kani_limit=25,lean_support_used=sum(r['kind']!='kani'for r in receipts),lean_support_limit=150,extraction_used=0,extraction_limit=0),uncredited_native=['K021 constructor positive: no matched control','K024 high positive: K025 matched control timed out'],interfaces='Both136 proposals ungated; value-only136 is too weak; proposed256 and conditional source step are not a child proof or parent native fold')
assert combined and combined[-1]['exit_status']==0 and len(combined)<=2
assert scans[-1]['exit_status']==0 and not a['dangling']and not a['conflicting_owners']and not a['import_mismatches']
assert not a['missing_raw_roots']and not a['unexpected_raw_roots']and not a['duplicate_raw_roots']and not nonstandard
assert len(fixtures)==8 and all(any(x not in standard for x in r['walked_axioms'])for r in fixtures)
assert all(r['root']=='NHC_DecodeModel.decoder_error'for r in disagreements)
assert all(x['status']=='PASS'for x in comparison.values())
(E/'NLI_AUDIT.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps({k:a[k]for k in ['status','modules','raw_result_count','raw_standard_axioms_only','budgets']}))
