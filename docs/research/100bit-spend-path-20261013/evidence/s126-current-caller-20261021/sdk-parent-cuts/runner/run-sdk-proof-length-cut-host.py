#!/usr/bin/env python3
"""Prove the actual frozen guard never reaches memcmp on any wrong runtime length.
Only memcmp's body is replaced by assert(false); assume(false), not by a
successful answer or an assumed comparison. All reachable source safety,
return/frame observations and unwinding assertions must still pass.
"""
from pathlib import Path
import os,sys,json,hashlib,subprocess,signal,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin');tag=sys.argv[1] if len(sys.argv)>1 else 'sdk-proof-length-cut-v1';O=H/tag
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frame='frame' in sys.argv[2:]
P=H/('sdk-proof-gate-v4' if frame else 'sdk-proof-gate-v2');pin=H/('sdk-proof-length-frame-codegen-v1-input.json' if frame else 'sdk-proof-gate-other-lengths-v1-input.json');old=json.loads(pin.read_text());assert old['source_sha256']==sha(P/'src/lib.rs')
wanted='proofs::actual_sdk_guard_other_lengths';line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn actual_sdk_guard_other_lengths()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_proof_gate*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']==wanted and row['original_start_line']==line and row['attributes']['kind']==({'ProofForContract':{'target_fn':'native_gate'}} if frame else 'Proof'):selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0];raw=Path(row['goto_file']);assert raw.is_file() and raw.name.endswith('.symtab.out')
source=Path(str(raw).replace('.symtab.out','.out'));assert source.is_file()
namesPath=Path(str(raw).replace('.symtab.out','.pretty_name_map.json'));names=json.loads(namesPath.read_text())
assert names.get('memcmp')=='memcmp';entry=[n for n,v in names.items() if v==wanted];assert len(entry)==1
libc=Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c')
commands=[
 [str(B/'goto-cc'),str(raw),str(libc),'-o',str(O/'linked.out')],
 [str(B/'goto-cc'),str(O/'linked.out'),'--function',entry[0],'-o',str(O/'entry.out')],
 [str(B/'goto-instrument'),'--add-library','--no-malloc-may-fail',str(O/'entry.out'),str(O/'library.out')],
 [str(B/'goto-instrument'),'--remove-function-body','memcmp',str(O/'library.out'),str(O/'removed.out')],
 [str(B/'goto-instrument'),'--generate-function-body','memcmp','--generate-function-body-options','assert-false-assume-false',str(O/'removed.out'),str(O/'cut.out')],
 [str(B/'goto-instrument'),'--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',str(O/'cut.out'),str(O/'reachable.out')],
 [str(B/'goto-instrument'),'--ensure-one-backedge-per-target',str(O/'reachable.out'),str(O/'ready.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','8','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'ready.out')]
]
if frame:
 assert row['contract'] and not row['contract']['recursion_tracker']
 commands.insert(2,[str(B/'goto-instrument'),'--dfcc',entry[0],'--no-malloc-may-fail','--enforce-contract',row['contract']['contracted_function_name'],str(O/'entry.out'),str(O/'contract.out')])
 commands[3][-2]=str(O/'contract.out')
if 'run' not in sys.argv:
 assert not O.exists();O.mkdir()
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),reused_compile_input_sha256=sha(pin),reused_compile_exit_status=json.loads((H/'receipts'/('sdk-proof-length-frame-codegen-v1' if frame else 'sdk-proof-gate-other-lengths-v1')/'receipt.json').read_text())['exit_status'],raw_goto_sha256=sha(raw),historical_prepared_goto_sha256=(sha(source) if source.exists() else None),kani_lib_c_sha256=sha(libc),harness_metadata_sha256=sha(metadata),harness_metadata=row,pretty_names_sha256=sha(namesPath),runner_sha256=sha(Path(__file__)),tool_pins={str(p):sha(p) for p in [B/'goto-cc',B/'goto-instrument',B/'cbmc',libc]},commands=commands,normal_pipeline_receipt_sha256=sha(H/'receipts/sdk-private-stub-semantic-preflight-v4/stdout.log'),preprocessing='Reconstruct the pinned normal Kani pipeline from raw symtab: link the actual bundled kani_lib.c, select harness, add CBMC library, assert-false undefined bodies, backedge normalization. Only memcmp receives an additional assert-false reachability cut; all source safety assertions remain.',cut='Only memcmp body -> assert(false); assume(false). Any reached comparison fails; this is a reachability proof, never an assumed equality.',property_scope='All reachable assertions and source observations, full unwinding checks; no property selection',qualification=__doc__,timeout_seconds=180),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Reuse exact source-pinned codegen; assert-unreachable comparator cut for full10MiB wrong-length guard, then at most180s CBMC; no compilation or byte-loop evaluation','--','python3',__file__,tag,'run',*(['frame'] if frame else [])]))
for i,cmd in enumerate(commands):
 with (O/('step'+str(i)+'.log')).open('w') as log:
  process=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:process.wait(timeout=180)
  except subprocess.TimeoutExpired:
   os.killpg(process.pid,signal.SIGKILL);process.wait();(O/'timeout.json').write_text(json.dumps(dict(command=cmd,status='not_proved',reason='180s timeout; no cap increase'))+'\n');raise
 if i<len(commands)-1:assert process.returncode==0,process.returncode
 else:
  rows=[]
  for item in json.loads((O/('step'+str(i)+'.log')).read_text()):
   rows += [{k:v for k,v in p.items() if k!='trace'} for p in item.get('result',[])]
  (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=process.returncode,qualification='Raw exit retained: reached cover reports FAILURE; every non-cover must be SUCCESS.'))+'\n')
  raise SystemExit(process.returncode)
