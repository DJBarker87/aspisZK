#!/usr/bin/env python3
"""Check exact frozen caller fission and cfg-only combined release erasure."""
from pathlib import Path
import subprocess,tempfile,json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';n='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
sha=lambda b:hashlib.sha256(b).hexdigest()
def span(s,name):
 a=s.index(name);i=s.index('{',a);depth=0
 for j in range(i,len(s)):
  if s[j]=='{':depth+=1
  if s[j]=='}':
   depth-=1
   if depth==0:return s[a:j+1]
 raise AssertionError('unterminated function')
def expected(frozen):
 ref=span(frozen,'pub fn validate_pool_v1_pair_forest_terminal_statement_v1(')
 ref=ref.replace('pub fn validate_pool_v1_pair_forest_terminal_statement_v1(', 'fn validator_ref(')
 ref=ref.replace('    statement: &PoolV1PairForestTerminalStatementV1,','    statement: &PoolV1PairForestTerminalStatementV1,\n    payment:Result<[u8;216],PoolV1PaymentStatementFormatError>,\n    lane:Result<u8,PoolV1PairForestAccountErrorV1>,\n    late:Result<(),PoolV1PairLatePublicStatementErrorV1>,\n    trace:&mut Trace,')
 for a,b in [('            encode_pool_v1_private_transfer_public_v1(public)','            trace.push(1);\n            payment'),('            encode_pool_v1_withdrawal_public_v1(public)','            trace.push(2);\n            payment'),('    let expected_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)','    trace.push(3);\n    let expected_lane = lane'),('    encode_pool_v1_pair_late_public_statement_v1(&common.lane_transition, &mut late_bytes)','    trace.push(4);\n    late')]:
  assert ref.count(a)==1;ref=ref.replace(a,b)
 return ref

def main():
 frozen=subprocess.check_output(['git','show',rev+':'+n],cwd=R,text=True)
 with tempfile.TemporaryDirectory(prefix='NED-bindings-') as d:
  b=Path(d);q=b/n;q.parent.mkdir(parents=True);q.write_text(frozen)
  for patch in ['NED_call_windows.patch','NED_bindings.patch']:subprocess.run(['git','apply',str(E/patch)],cwd=b,check=True,capture_output=True)
  module_path=b/'crates/aspis-statement/src/pool_v1/NED_bindings.rs';before_extra=module_path.read_text()
  subprocess.run(['git','apply',str(E/'NED_binding_extra.patch')],cwd=b,check=True,capture_output=True)
  module=module_path.read_text();assert module.startswith(before_extra)
  subprocess.run(['git','apply',str(E/'NED_decode_windows.patch')],cwd=b,check=True,capture_output=True)
  actual=span(module,'fn validator_ref(');assert actual==expected(frozen)
  bad=actual.replace('::HistoricalAnchorMismatch','::CheckpointBindingMismatch');assert bad!=expected(frozen)
  bad=actual.replace('trace.push(3)','trace.push(4)');assert bad!=expected(frozen)
  text=q.read_text();hook='\n#[cfg(kani)]\n#[path="NED_bindings.rs"]\nmod NED_bindings;\n\n'
  assert text.count(hook)==1;text=text.replace(hook,'')
  decode_hook='\n#[cfg(kani)]\n#[path="NED_decode_windows.rs"]\nmod NED_decode_windows;\n\n'
  assert text.count(decode_hook)==1;text=text.replace(decode_hook,'')
  lines=text.splitlines(True);out=[];i=0
  while i<len(lines):
   if lines[i].strip()=='#[cfg(kani)]' and ('NED_windows::' in lines[i+1] or 'NED_decode_windows::' in lines[i+1] or lines[i+1].strip() in ['#[path="NED_windows.rs"]','#[path="NED_decode_windows.rs"]']):
    i+=3 if lines[i+1].strip().startswith('#[path=') else 2
   else:out.append(lines[i]);i+=1
  assert ''.join(out)==frozen+'\n'
  report=dict(erasure_exact=True,frozen_revision=rev,frozen_file_sha256=sha(frozen.encode()),reference_exact_frozen_cut=True,reference_sha256=sha(actual.encode()),patch_sha256=sha((E/'NED_bindings.patch').read_bytes()),extra_patch_sha256=sha((E/'NED_binding_extra.patch').read_bytes()),decode_patch_sha256=sha((E/'NED_decode_windows.patch').read_bytes()),mutation_wrong_error_rejected=True,mutation_wrong_call_order_rejected=True,scope='binding probes and opaque caller Result/call-order only; no functional stub law inferred')
  print(json.dumps(report,indent=1))
if __name__=='__main__':main()
