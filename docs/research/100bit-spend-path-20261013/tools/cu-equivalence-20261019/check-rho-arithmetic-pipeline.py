#!/usr/bin/env python3
"""Validate focused arithmetic receipts; never claim missing caller admission."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
ev=area/'evidence/cu-equivalence-20261019';started=time.monotonic()
sha=lambda b:hashlib.sha256(b).hexdigest()
checks={}
for script in ['extract-rho-reference-step.py','emit-rho-reference-step.py','extract-rho-accumulate.py']:
    result=subprocess.run([sys.executable,str(here/script),'--check'],check=True,capture_output=True,text=True)
    checks[script]=dict(sha256=sha((here/script).read_bytes()),result=json.loads(result.stdout))
targets={
    'AspisR1RhoReference/Funs':'rho-reference-step-funs-b',
    'CuSavingsRhoReference':'rho-reference-proof-c',
    'CuSavingsRhoVector':'rho-vector-c',
    'CuSavingsRhoQueryBatch':'rho-query-batch-b',
    'CuSavingsRhoBatches':'rho-batches-a'}
success={};objects={}
for module,attempt in targets.items():
    source=area/'lean'/(module+'.lean');snapshot=ev/attempt/'source.lean'
    receipt_path=ev/attempt/'receipt.json';receipt=json.loads(receipt_path.read_text())
    assert receipt['exit_status']==0 and receipt['source_sha256']==sha(source.read_bytes())==sha(snapshot.read_bytes())
    assert receipt['object_sha256']
    log=(ev/attempt/'stdout.log').read_text();assert log==receipt['print_axioms_output']
    assert not re.search(r'\berror:|sorryAx|\badmit\b',log)
    names=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
    assert names
    for name,axioms in names:
        assert set(filter(None,axioms.replace(' ','').split(','))) <= {'propext','Classical.choice','Quot.sound'},name
    objects[module.replace('/','.')]=receipt['object_sha256']
    success[module]=dict(attempt=attempt,source_sha256=receipt['source_sha256'],receipt_sha256=sha(receipt_path.read_bytes()),
        declarations=[name for name,_ in names],exit=0,wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],
        process_swaps=receipt['process_swaps'],cgroup_swap_bytes=receipt['cgroup_swap_bytes'])
for attempt in targets.values():
    receipt=json.loads((ev/attempt/'receipt.json').read_text())
    for item in receipt['direct_imports']:
        if item['module'] in objects:assert item['sha256']==objects[item['module']]
emissions={}
for attempt in ['rho-reference-step-charon-b','rho-reference-step-aeneas-b','rho-accumulate-charon-a']:
    receipt=json.loads((ev/attempt/'receipt.json').read_text());assert receipt['exit_status']==0
    emissions[attempt]=dict(exit=0,wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],
        process_swaps=receipt['process_swaps'],receipt_sha256=sha((ev/attempt/'receipt.json').read_bytes()))
failures={}
for attempt in ['rho-aeneas-init-reference-a','rho-accumulate-aeneas-a']:
    receipt=json.loads((ev/attempt/'receipt.json').read_text());assert receipt['exit_status']!=0
    failures[attempt]=dict(exit=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],
        peak_rss_kib=receipt['peak_rss_kib'],process_swaps=receipt['process_swaps'],
        receipt_sha256=sha((ev/attempt/'receipt.json').read_bytes()),status='NOT_ADMITTED')
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='ARITHMETIC_PIPELINE_CHECKED_CALLER_ADMISSION_OPEN',
    candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611',
    production_revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9',
    source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
    command=[sys.executable,str(Path(__file__).resolve())],features=['pool-adapter','private-leaf-salts'],checks=checks,
    focused_successes=success,source_emissions=emissions,failed_source_emissions=failures,
    tool_sha256={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',
        'aeneas_original_reference':'4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'},
    scope='Exact old coefficient source step equals the complete checked optimized push; fresh-coordinate vector composition, checked query counter increment and finite arithmetic pipeline through actual finish, including arbitrary inter-query failures/divergence. Initial-state list model is explicitly not new/zip source admission.',
    still_required=['Actual new/zip and sufficient-resource allocation admission',
        'Actual accumulate_with_node basis/index sequence and canonicality admission',
        'Actual transaction/query/checkpoint/observation caller composition'],
    candidate_complete=False,combined_security_transfer_complete=False,
    audit=dict(exit=0,wall_seconds=time.monotonic()-started,
        peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,
        process_swaps=usage.ru_nswap,print_axioms='N/A: receipt/source audit only; individual Lean results above'))
(ev/'RHO-ARITHMETIC-PIPELINE.json').write_text(json.dumps(report,indent=2)+'\n')
print(report['status'])
