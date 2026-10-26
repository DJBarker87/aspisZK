#!/usr/bin/env python3
"""Audit exact source substitution, snapshot range and resource countermodel."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
O=E/'s6-source-budget-integration-v1'
sha=lambda b:hashlib.sha256(b).hexdigest();load=lambda p:json.loads(p.read_text())
m=load(O/'manifest.json')
reports=0
for name,attempt in m['targets'].items():
 a=E/attempt;r=load(a/'receipt.json');source=S/(name+'.lean')
 assert r['exit_status']==0 and r['swaps']==0
 assert sha(source.read_bytes())==sha((a/'source.lean').read_bytes())==r['source_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command'] and r['print_axioms']
 for report in r['print_axioms']:
  match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
  assert match and set(re.findall(r'[A-Za-z_.]+',match[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source.read_text(),re.M)
 for direct,pin in r['direct_imports'].items():assert pin['sha256'] and pin['path']
for path,pin in m['reused_source_pins'].items():assert sha((R/path).read_bytes())==pin
for path,pin in m['immutable_research_pins'].items():
 value=subprocess.check_output(['git','show',m['research_revision']+':'+path],cwd=R)
 assert sha(value)==pin
 assert (O/'reviewed-source'/path).read_bytes()==value
for attempt in m['excluded_failed_attempts']:
 r=load(E/attempt/'receipt.json');assert r['exit_status']!=0
source=(S/'S6CurrentDirectDecoderV1.lean').read_text()
assert 'theorem stage1_eq' in source and 'theorem install_eq' in source
assert '(accepted :' not in source and '(decoded :' not in source
source=(S/'S6SnapshotBudgetV1.lean').read_text()
assert 'theorem allocate_snapshots_headroom' in source and 'theorem snapshot_success_not_child_admission' in source
assert '61943' in source and '200201' in source and '262144' in source
assert not m['whole_s6_closed'] and not m['actual_bump_allocator_instantiated']
assert m['enclosing_premises_removed']==0
print(json.dumps({'status':'PASS','targets':len(m['targets']),'standard_axiom_reports':reports,'complete_stage1_source_result_equality':True,'represented_snapshot_requested_bytes_upper_bound':61943,'requested_byte_model_headroom_from_256KiB':200201,'snapshot_success_alone_implies_child_headroom':False,'actual_bump_allocator_instantiated':False,'enclosing_premises_removed':0,'whole_s6_closed':False}))
