from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;standard={'propext','Classical.choice','Quot.sound'};known={'AspisR1.NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
manifest=json.loads((E/'NLU_AUDIT_ROOTS.json').read_text());wanted=set(manifest['roots']);results=[];groups=[]
for p in sorted((E/'NLU_audit').glob('proof*/proof*.json')):
 x=json.loads(p.read_text());results+=x['results'];groups.append(dict(target=x['target'],exit=x['exit_status'],roots=len(x['results'])))
seen={x['root'] for x in results};bad=[x for x in results if not set(x['walked_axioms'])<=standard];diffs=[x for x in results if not x['equal']];unknown=[x for x in diffs if x['root'] not in known]
loaded=[json.loads(s) for s in (E/'NLU_LOADED_scan.jsonl').read_text().splitlines()];scan_bad=[x for x in loaded if x['dangling'] or x['duplicate_owners'] or not x['imports_match']]
fixtures=json.loads((E/'NLU_audit/fixtures/fixtures.json').read_text());comparison=json.loads((E/'NLU_PREDECESSOR_COMPARISON.json').read_text());pins_ok=all(not x['mismatches'] for x in comparison.values());compile_receipt=json.loads((E/'NLU_L111/receipt.json').read_text());scan_receipt=json.loads((E/'NLU_L117/receipt.json').read_text())
raw_ok=len(groups)==31 and seen==wanted and not bad and not unknown
passed=compile_receipt['exit_status']==0 and scan_receipt['exit_status']==0 and not scan_bad and fixtures['exit_status']==0 and len(fixtures['results'])==8 and raw_ok and pins_ok
attempts=[json.loads(p.read_text()) for p in E.glob('NLU_L*/receipt.json')];native=[json.loads(p.read_text()) for p in E.glob('NLU_K*/receipt.json')]
admissions=[]
for p in E.glob('NLU_[LK][0-9][0-9][0-9]-admission.json'):
 x=json.loads(p.read_text());admissions.append(x['exit']==0 and x['reservation']['allowed'] is True)
assert all(admissions),'Non-admitted submitted scope'
refs=json.loads((E/'NLU_GRAPH_REFS.json').read_text())
for n,x in refs.items():assert hashlib.sha256(lzma.decompress((E/x['archive']).read_bytes())).hexdigest()==x['sha256']
record=dict(status='PASS_SUPPORT_GATE' if passed else 'FINDING',native_root=None,row='TX1:136',row_status='OPEN',new_closed_rows=0,target_not_yet_established=True,combined_exit=compile_receipt['exit_status'],combined_target='NLU_COMBINED_IMPORT',combined_campaigns=1,raw_groups=groups,expected_roots=len(wanted),observed_roots=len(seen),missing_roots=sorted(wanted-seen),unexpected_roots=sorted(seen-wanted),nonstandard=bad,collector_disagreements=diffs,unknown_collector_disagreements=unknown,raw_standard_complete=raw_ok,loaded_modules=len(loaded),scan_exit=scan_receipt['exit_status'],scan_defects=len(scan_bad),fixtures_exit=fixtures['exit_status'],fixture_controls=len(fixtures['results']),predecessor_comparison=comparison,pins_pass=pins_ok,budget=dict(lean_support=len(attempts),kani=len(native),extraction=0),all_submitted_admissions_pass=True,graphs_retained_once_by_sha=True,trust_changes=[],frozen_verifier='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_pool='b936275465',release_pool_elf='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',headline='AspisR1.RPx_Deployed.deployed',limitations=['No native parent heap/cut/lifecycle fold or136 root','Not a cold frozen-release replay','Source/component support is not composed ledger credit'])
(E/'NLU_AUDIT.json').write_text(json.dumps(record,indent=1));print(json.dumps({k:record[k] for k in ['status','expected_roots','observed_roots','loaded_modules','scan_defects','raw_standard_complete','budget','new_closed_rows']}))
