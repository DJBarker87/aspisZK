#!/usr/bin/env python3
"""Paired accepted-parent check under one named pure std-any overapproximation.
This is not an unconditional source theorem: exact scan/byte-view and child
interpretations must be composed from separately checked certificates.
Raw CBMC assertion/cover statuses and exit are retained without re-labelling.
"""
from pathlib import Path
import sys,os,re,json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin');tag=sys.argv[1] if len(sys.argv)>1 else 'sdk-paired-context-check-v1';O=H/tag;O.mkdir(exist_ok=True)
mode='prefix' if 'prefix' in tag else ('native' if 'native' in tag else 'paired')
files=list((H/'target/kani').rglob('aspis_s126_sdk_'+mode+'_context_v1*pretty_name_map.json'));assert len(files)==1,files
names=json.loads(files[0].read_text());selected=[(k,v) for k,v in names.items() if '::any::' in str(v) and 'u8' in str(v) and 'stage1' in str(k)];assert len(selected)==1,selected
scan,pretty=selected[0];entries=[k for k,v in names.items() if v==('proofs::'+mode+'_parent_arguments' if mode!='paired' else 'proofs::paired_parent_context')];assert len(entries)==1,entries
source=Path(str(files[0]).replace('.pretty_name_map.json','.out'));assert source.is_file()
commands=[
 [str(B/'goto-instrument'),'--remove-function-body',scan,str(source),str(O/'removed.out')],
 [str(B/'goto-instrument'),'--generate-function-body',re.escape(scan),'--generate-function-body-options','nondet-return',str(O/'removed.out'),str(O/'abstract.out')],
 [str(B/'goto-cc'),str(O/'abstract.out'),'--function',entries[0],'-o',str(O/'entry.out')],
 [str(B/'goto-instrument'),'--add-library','--no-malloc-may-fail',str(O/'entry.out'),str(O/'library.out')],
 [str(B/'goto-instrument'),'--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',str(O/'library.out'),str(O/'reachable.out')],
 [str(B/'goto-instrument'),'--ensure-one-backedge-per-target',str(O/'reachable.out'),str(O/'ready.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','1772','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'ready.out')]
]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if len(sys.argv)<3:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',commands=commands,input_goto_sha256=sha(source),pretty_names_sha256=sha(files[0]),abstracted_function=scan,pretty_name=pretty,tool_pins={str(p):sha(p) for p in [B/'goto-instrument',B/'goto-cc',B/'cbmc']},qualification=__doc__,timeout_seconds=180,preprocessing='Kani normal goto-cc harness entry, add-library, assert-false undefined bodies, reachable pruning, backedge normalization; all Rust/CBMC safety and unwinding checks retained',normal_pipeline_receipt_sha256=sha(H/'receipts/sdk-private-stub-semantic-preflight-v4/stdout.log')),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Cached paired parent GOTO: transform only named pure any; then one 180s bounded CBMC context assertion/cover check; no arithmetic evaluation','--','python3',__file__,tag,'run']))
for i,command in enumerate(commands):
 with (O/('step'+str(i)+'.log')).open('w') as output:
  try:p=subprocess.run(command,stdout=output,stderr=subprocess.STDOUT,timeout=180)
  except subprocess.TimeoutExpired:
   (O/'timeout.json').write_text(json.dumps(dict(command=command,timeout_seconds=180,qualification='No proof completion; explicit timed-out context, do not accept.'))+'\n');raise
 if i<len(commands)-1:assert p.returncode==0,p.returncode
 else:
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,qualification='Raw CBMC exit retained; covers are counterexample reachability checks, not silently converted into successful assertion status.'))+'\n')
  try:
   data=json.loads((O/('step'+str(i)+'.log')).read_text());rows=[]
   for item in data:
    for row in item.get('result',[]):rows.append({k:v for k,v in row.items() if k!='trace'})
   (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
  except (ValueError,TypeError):pass
  raise SystemExit(p.returncode)
