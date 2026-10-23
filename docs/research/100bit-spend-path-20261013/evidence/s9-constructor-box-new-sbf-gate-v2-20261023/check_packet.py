#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-sbf-stack-gate-packet-v1'
assert m['status']=='candidate-own-frame-stack-gate-passed-whole-program-stack-gate-failed'
assert m['candidate_stack_gate_pass'] is True and m['whole_program_stack_gate_pass'] is False
assert m['scope_limits_bytes']=={'memory_high':3221225472,'memory_max':4294967296,'memory_swap_max':0}
assert m['v1_v2_stack_warning_comparison']=={'v1_count':35,'v2_count':34,'common_unchanged':34,'removed_only_candidate_new':1,'added':0,'changed_common':0}
for row in m['files']:
 p=root/row['path']; assert p.is_file(),row['path']; data=p.read_bytes()
 assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],row['path']
 assert p.suffix not in {'.so','.o','.rlib','.olean','.llbc'},row['path']
assert hashlib.sha256((root/'source/weights.base.rs').read_bytes()).hexdigest()==m['base_weights_sha256']
assert hashlib.sha256((root/'source/weights.candidate.rs').read_bytes()).hexdigest()==m['candidate_weights_sha256']
log=(root/'build/build.log').read_text(); pat=re.compile(r'^Error: Function (\S+) Stack offset of (\d+) exceeded max offset of (\d+) by (\d+) bytes',re.M); rows=pat.findall(log)
assert len(rows)==34 and not any('Weights::new' in x[0] or 'Weights::box_from_parts' in x[0] for x in rows)
assert 'Finished `release` profile' in log
cmp=json.loads((root/'build/stack-warning-comparison.json').read_text())
assert cmp['removed']==[m['baseline_v1_diagnostic_removed'].split(':')[0]] and cmp['added']==[] and cmp['changed_common']==[]
audit=(root/'build/reachable-stack-audit.txt').read_text()
assert 'Weights::box_from_parts::hcfab457221f1219c' in audit and 'Weights::new::h76fb764f043335f7' in audit
assert 'Weights::box_from_parts::hcfab457221f1219c' in audit.split('Reachability relocation evidence:')[1]
assert '0000000000004700 R_SBF_64_32' in audit
assert not any(p.suffix=='.so' for p in root.rglob('*'))
print('PASS: v2 constructor symbols reachable, own stack warnings removed, unrelated whole-program stack gate failure retained')
