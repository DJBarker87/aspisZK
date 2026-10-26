#!/usr/bin/env python3
"""Audit receipts/statements/source association without replaying compilers."""
from pathlib import Path
import hashlib
import json
import re

R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021'
S=B/'lean-candidates/s126-caller-boundary-20261021'
O=E/'s6-bump-step-terminal-v1'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(O/'manifest.json')
for path,pin in m['source_files'].items():assert sha(O/path)==pin,path
for case,expected in [('positive',0),('negative',1)]:
    a=E/m[case];r=load(a/'receipt.json');i=load(a/'input.json');log=(a/'stdout.log').read_text()
    assert r['exit_status']==expected and r['swaps']==0 and r['watchdog_stop'] is None
    assert r['source_unchanged'] and r['imports_unchanged'] and r['tools_unchanged']
    assert r['input_sha256']==sha(a/'input.json') and r['stdout_sha256']==sha(a/'stdout.log')
    assert i['environment']['RUSTFLAGS']=='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes'
    assert i['guard']['aggregate_rss_max_bytes']==4*2**30
    assert not i['import_pins'] # The only library boundary is the pinned tool std.
    for path,pin in i['source_pins'].items():assert sha(O/m['source_workspace']/path)==pin,path
    if case=='positive':
        assert '0 of 116 failed' in log and '4 of 4 cover properties satisfied' in log
    else:
        assert '1 of 116 failed' in log
        assert 'Failed Checks: assertion failed: actual as usize == start + expected' in log
workspace=O/m['source_workspace']
binding=load(workspace/'binding.json');original=(workspace/'sdk-original.rs').read_text()
body=original[original.index(binding['copied_begin_marker']):original.index(binding['copied_end_marker'])]
assert hashlib.sha256(body.encode()).hexdigest()==binding['copied_declarations_sha256']
assert (workspace/'harness/src/shipped.rs').read_text()=='use core::{alloc::Layout,mem::size_of,ptr::null_mut};\n\n'+body
assert (workspace/'harness/src/lib.rs').read_bytes()==(R/'tools/s6-bump-step-20261026/proof.rs').read_bytes()
for name,attempt in [('S6AlignedAllocationRangeV1','s6-aligned-allocation-range-v1'),
                     ('S6SdkAcceptedExtractionV1','s6-sdk-accepted-extraction-v1')]:
    a=E/attempt;r=load(a/'receipt.json')
    assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
    assert sha(S/(name+'.lean'))==sha(a/'source.lean')==r['source_sha256']
    for report in r['print_axioms']:
        match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
        assert match and set(re.findall(r'[A-Za-z_.]+',match[1]))<={'propext','Classical.choice','Quot.sound'}
    assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',(S/(name+'.lean')).read_text(),re.M)
before=(S/'S6SdkFirstOnlyV1.lean').read_text();before=before[before.index('theorem original_sdk_reached_first '):before.index('\n#print axioms stage1_of_full')]
after=(S/'S6SdkAcceptedExtractionV1.lean').read_text();after=after[after.index('theorem original_sdk_reached_first_accepted_extraction '):after.index('\n\n#print axioms of_full')]
expected=before.replace('theorem original_sdk_reached_first ','theorem original_sdk_reached_first_accepted_extraction ')
expected=expected.replace('(stage1 : Stage1Extraction (install ops vops) native1)','(stage1 : AcceptedStage1Extraction (install ops vops) native1)')
expected=expected.replace('have owned := (stage1 program e.first data).symm.trans native','have owned := stage1 program e.first data saved native')
assert after==expected # Same conclusions, carriers, quantifiers and all other premises.
inventory=load(E/'s6-allocation-backbone-v1/inventory.json')
assert inventory['conditional_raw_decoder_box_bound']==5
assert len(inventory['exact_source_text_matches'])==165
assert len(inventory['no_source_text_functions'])==3
assert not inventory['native_allocation_bound_proved'] and not m['whole_s6_closed']
print(json.dumps({'status':'PASS','actual_sdk_allocator_step_checked':True,
                  'aligned_reference_induction_checked':True,
                  'complete_enclosing_conclusions_unchanged':True,
                  'full_stage1_equality_weakened_to_accepted_direction':True,
                  'concrete_stage1_instance_proved':False,
                  'native_to_lean_reference_extraction_proved':False,
                  'native_footprint_proved':False,'enclosing_premises_removed':0,'whole_s6_closed':False}))
