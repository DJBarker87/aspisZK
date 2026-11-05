from pathlib import Path
import json,hashlib,re
from NGY_io import read,text
E=Path(__file__).resolve().parent
roots=read(E/'NGY_AUDIT_ROOTS.json')['roots'];raw=read(E/'NGY_audit/batch0/proof0.json');fixtures=read(E/'NGY_audit/fixtures/fixtures.json')
scan=[json.loads(l) for l in (E/'NGY_LOADED_scan.jsonl').read_text().splitlines()]
statements=[json.loads(l.split('NGY_CERT_ENTRY ',1)[1]) for l in text(E/'NGY_L029/stdout.log').splitlines() if 'NGY_CERT_ENTRY ' in l]
std={'propext','Classical.choice','Quot.sound'}
assert len(raw['results'])==len(roots) and {r['root'] for r in raw['results']}==set(roots)
assert all(set(r['walked_axioms'])<=std for r in raw['results'])
assert len(fixtures['results'])==8 and all(r['equal'] for r in fixtures['results'])
counts=dict(modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan))
assert not(counts['dangling'] or counts['incompatible_owners'] or counts['import_mismatches'])
owners=read(E/'NGY_STATEMENT_ROOTS.json');assert len(statements)==len(owners) and all(owners[r['name']]==r['owner'] for r in statements)
(E/'NGY_TYPES.json').write_text(json.dumps(statements,indent=1)+'\n')
(E/'NGY_SCAN.json').write_text(json.dumps(counts,indent=1)+'\n')
# Compare selected unchanged walker object to the previously accepted NGU driver.
old=[]
for line in (E.parent/'prepared-claim-20261105/NGU_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r.get('module')=='NGU_ProofDriver' and r.get('kind')=='lean' and r['exit_status']==0:old.append(read(E.parent/'prepared-claim-20261105'/r['attempt']/'receipt.json'))
new=read(E/'NGY_L020/receipt.json')
walker=lambda r:{Path(v['path']).name:v['sha256'] for v in r['deps_fingerprint']['selected_objects'].values() if '/NFA_WALKER.' in v['path']}
assert old and walker(new)==walker(old[-1]) and walker(new)
result=dict(row='TX1:193',headline='AspisR1.RPx_Deployed.deployed',route='CLOSED under (ah)',raw_complete=True,raw_standard_only=True,raw_roots=len(raw['results']),collect_axioms_disagreements=sum(not r['equal'] for r in raw['results']),fixtures_pass=True,fixtures=fixtures,scan_clean=True,scan=counts,checked_kernel_types=len(statements),types='NGY_TYPES.json',walker_source=read(E/'NGY_WALKER_PIN.json'),walker_object_pins=walker(new),walker_matches_admitted_NGU_object=True,raw_receipt='NGY_L030/receipt.json',raw_data='NGY_audit/batch0/proof0.json',fixtures_data='NGY_audit/fixtures/fixtures.json',scan_data='NGY_LOADED_scan.jsonl',final_attempts=['NGY_L027','NGY_L028','NGY_L029','NGY_L030','NGY_L031'],scan_receipt='NGY_L031/receipt.json',fixtures_receipt='NGY_L024/receipt.json',source_revision_pins='NGY_ATTEMPTS.jsonl and full receipts',cold_release_replay=False,security_target_established=False,hand_transcription='P6/D188 option A reviewed-transcription RECLASSIFICATION; no trust removed')
(E/'NGY_AUDIT.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(raw_roots=result['raw_roots'],types=len(statements),scan=counts)))
