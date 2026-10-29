"""Offline final evidence consistency audit; no compiler, network, or host writes."""
from pathlib import Path
import hashlib,json,lzma,re
E=Path(__file__).resolve().parent
R=E.parents[1]
def read(name):return json.loads((E/name).read_text())
def sha(raw):return hashlib.sha256(raw).hexdigest()
result=read('NDR_FINAL_RESULT.json');receipt=read('NDR_A001/receipt.json')
assert result['exit_status']==receipt['exit_status']==0
assert result['source_revision']==receipt['source_revision']=='6a157d7757046c5381438a07888844117957d997'
assert result['budget_used']=={'single_module':11,'chunk_scopes':29,'agg16':1}
assert str(result['swaps'])=='0'
assert result['limits']=={'memory.high':'15032385536','memory.max':'17179869184','memory.swap.max':'0','pids.max':'64'}
assert result['strict_NDO_Joint_module_import'] is False
assert result['full_security_target_established'] is False
assert len(receipt['print_axioms'])==11
standard={'propext','Classical.choice','Quot.sound'}
for line in receipt['print_axioms']:
    m=re.search(r'depends on axioms: \[([^]]*)\]',line)
    assert m and set(m[1].split(', '))<=standard
source=(R/'lean/NDR_CombinedAudit.lean').read_text()
pack=read('NDR_AGGREGATION_PACKAGING.json')
assert sha(source.encode())==pack['source_sha256']==receipt['source_hashes']['NDR_CombinedAudit.lean']
blocked={row['module'] for row in pack['bodies']}
assert len(blocked)==5
for row in pack['bodies']:
    original=(R/'lean'/(row['module']+'.lean')).read_text()
    body=''.join(line for line in original.splitlines(keepends=True) if not line.startswith('import '))
    embedded=source.split('-- BEGIN verbatim body from '+row['module']+'.lean\n',1)[1].split('\n-- END verbatim body from '+row['module']+'.lean\n',1)[0]
    assert sha(original.encode())==row['source_sha256']
    assert body==embedded and sha(body.encode())==row['verbatim_body_sha256']
for row in read('NDR_SOURCE_PINS.json'):
    assert sha((R/'lean'/(row['module']+'.lean')).read_bytes())==row['sha256']
normal=read('NDR_VERIFICATION.json')
assert normal['passing_modules']==3113 and normal['planned_modules']==3118
assert set(normal['missing_modules'])==blocked
assert normal['completed_chunk_receipts']==29 and normal['failed_chunks']==['NDR_B020','NDR_B027']
assert len(read('NDR_BUILD_RECEIPTS.json'))==29
actual=read('NDR_KERNEL_IMPORTS.json')
assert len(actual)==len(set(actual))==16057
assert set(actual)==set(read('NDR_FINAL_IMPORT_PLAN.json'))
cohort=read('NDR_FINAL_COHORT_PINS.json')
assert {row['module'] for row in cohort['entries']}==set(actual)
assert len(cohort['additional_direct_import_artifacts'])==3
provenance=read('NDR_PROVENANCE.json')
assert len(provenance['entries'])==76
assert all(row['historical'] not in actual and row['kernel_exclusion_verified'] for row in provenance['entries'])
log=(E/'NDR_A001/stdout.log').read_text()
assert set(re.findall(r'NDR_HISTORICAL_OBJECT_EXCLUDED (\S+)',log))=={x['historical'] for x in provenance['entries']}
assert log.count('NDR_SAME_WRAPPER_CONSTANTS ')==2 and log.count('NDR_TREE_BINDER_RETAINED ')==3
assert 'NDR_JOINT_RUNTIME_PREMISE_RETAINED' in log and 'NDR_COMBINED_COMPLETE' in log
assert read('NDR_AGG16_RUNNER_HASHES.json')['match'] is True
assert len(read('NDR_AGG16_RUNNER_HASHES.json')['expected'])==3
for attempt in ['NDR_A001']+[f'NDR_L{i:03d}' for i in range(1,6)]+[f'NDR_B{i:03d}' for i in range(1,30)]:
    assert read(attempt+'-reservation.json')['allowed'] is True
ledger=[json.loads(line) for line in (E/'NDR_ATTEMPTS.jsonl').read_text().splitlines()]
compiled=[row for row in ledger if row.get('kind')=='lean']
assert len({row['attempt'] for row in compiled})==35
assert len([row for row in compiled if row['attempt'].startswith('NDR_A')])==1
for row in ledger:
    if row.get('kind')=='admission':assert row['exit_status']==0 and row['allowed'] is True
    if row.get('full_receipt'):assert sha((E/row['full_receipt']).read_bytes())==row['full_receipt_sha256']
for stem in ['NDR_ATTEMPTS_full_through_B024.jsonl','NDR_BUILD_RECEIPTS_full_through_B020.json']:
    assert sha(lzma.decompress((E/(stem+'.xz')).read_bytes()))==(E/(stem+'.sha256')).read_text().split()[0]
assert all(f.stat().st_size<=20000000 for f in E.rglob('*') if f.is_file())
print(json.dumps(dict(status='PASS',standalone_modules=3113,verbatim_final_bodies=5,kernel_import_modules=16057,historical_exclusions=76,standard_final_axiom_lines=11,strict_standalone_packaging_complete=False,full_security_target_established=False)))
