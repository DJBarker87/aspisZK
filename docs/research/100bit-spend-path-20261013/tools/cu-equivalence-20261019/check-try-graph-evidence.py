#!/usr/bin/env python3
"""Check retained graph-metadata receipts; this does not admit a compiler pass."""
from pathlib import Path
import hashlib,json,subprocess,sys
here=Path(__file__).resolve().parent
area=here.parents[1]; evidence=area/'evidence/cu-equivalence-20261019'
sha=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
read=lambda path:json.loads(path.read_text())
build_dir=evidence/'aeneas-try-graph-build-a/build'
build=read(build_dir/'receipt.json')
binary='c0d5cbc1676c3ab85ffc0b00e6ee440dd6dca3e02573a181ca9766d65ee01d6b'
assert build['exit_status']==0 and build['binary_sha256']==binary
assert build['process_swaps']==0 and build['last_cgroup_observation']['memory.swap.current']=='0'
assert build['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
assert sum(value for _,value in build['reservations_before_create'])+8*2**30<=50*2**30
assert sum(value for _,value in build['reservations_at_compile_gate'])<=50*2**30
assert sha(build_dir/'try-graph-metadata.patch')==build['pins']['patch_sha256']
assert sha(build_dir/'build.sh')==build['pins']['build_script_sha256']
assert sha(here/'build-aeneas-try-graph.py')==build['pins']['controller_sha256']
assert sha(here/'aeneas-try-graph-metadata.ml')==build['pins']['helper_sha256']
for attempt in ['aeneas-try-graph-build-a','array-try-graph-emission-a','try-graph-regression-a']:
    receipt=read(evidence/attempt/'receipt.json')
    assert receipt['exit_status']==0 and receipt['process_swaps']==0
    assert receipt['cgroup_swap_current']=='0' and not receipt['mandatory_review_stop']
    assert receipt['limits']['memory.swap.max']=='0'
    assert sum(value for _,value in receipt['reservations'])<=50*2**30
controller=read(evidence/'aeneas-try-graph-build-a/receipt.json')
assert controller['limits']['memory.max']==str(2**30)
reg_dir=evidence/'try-graph-regression-a/cases';reg=read(reg_dir/'summary.json')
assert reg['exit_status']==0 and len(reg['cases'])==66
assert reg['harness_sha256']==sha(here/'check-try-graph-emission.py')
for case in reg['cases']:
    directory=reg_dir/case['name']
    assert case==read(directory/'receipt.json')
    assert case['passed'] and case['exit_status']==case.get('expected_exit',0)
    assert case['process_swaps']==0 and case['frontend_binary_sha256']==binary
    assert '-checks' in case['command']
    if 'expected_files' in case:
        actual={p.name:sha(p) for p in (directory/'generated'/case['namespace']).glob('*.lean')}
        assert actual==case['actual_files']==case['expected_files']
    if 'expected_error' in case:
        assert case['expected_error'] in ((directory/'stdout.log').read_text()+(directory/'stderr.log').read_text())
full=[case for case in reg['cases'] if case['name']=='full-library-emission-graph-1'][0]
for name,pin in full['actual_files'].items():
    assert sha(here/'array-graph-generated'/name)==pin
layout=json.loads(subprocess.check_output([sys.executable,str(here/'emit-array-graph.py'),'--check'],text=True))
print(json.dumps(dict(status='CHECKED_SOURCE_AND_RECEIPTS_ONLY',cases=66,metadata_binary_sha256=binary,
    layout=layout,source_admission_complete=False,security_transfer_complete=False)))
