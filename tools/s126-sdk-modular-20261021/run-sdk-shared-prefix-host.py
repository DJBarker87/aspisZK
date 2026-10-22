#!/usr/bin/env python3
"""Actual native SDK decoder-entry frame and same-allocation reference cut.
Only the exact native pure std-any is overapproximated by a read-only Boolean
return. The native write frame is explicitly DFCC-enforced before linking the
CBMC library. No byte equality is assumed; no property is selected or dropped.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,os,signal,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin')
havoc_inputs='havoc-inputs' in sys.argv
tag,version=sys.argv[1:3];P=H/('sdk-shared-prefix-'+version);O=H/tag
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=H/('sdk-shared-prefix-codegen-'+version+'-input.json');inp=json.loads(pin.read_text())
assert sha(P/'src/lib.rs')==inp['source_sha256']
wanted='proofs::native_owned_decoder_prefix';line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn native_owned_decoder_prefix()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_shared_prefix*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']==wanted and row['original_start_line']==line and row['attributes']['kind']=={'ProofForContract':{'target_fn':'native_prefix'}}:selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0];raw=Path(row['goto_file']);assert raw.is_file() and raw.name.endswith('.symtab.out')
assert row['contract'] and not row['contract']['recursion_tracker']
namePath=Path(str(raw).replace('.symtab.out','.pretty_name_map.json'));names=json.loads(namePath.read_text())
scans=[(k,v) for k,v in names.items() if '::any::' in str(v) and 'u8' in str(v) and 'stage1' in k];assert len(scans)==1,scans
scan,pretty=scans[0];entries=[k for k,v in names.items() if v==wanted];assert len(entries)==1
entry=entries[0];libc=Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c')
cmds=[
 [str(B/'goto-cc'),str(raw),str(libc),'-o',str(O/'linked.out')],
 [str(B/'goto-instrument'),'--remove-function-body',scan,str(O/'linked.out'),str(O/'removed.out')],
 [str(B/'goto-instrument'),'--generate-function-body',re.escape(scan),'--generate-function-body-options','nondet-return',str(O/'removed.out'),str(O/'abstract.out')],
 [str(B/'goto-cc'),str(O/'abstract.out'),'--function',entry,'-o',str(O/'entry.out')],
 [str(B/'goto-instrument'),'--dfcc',entry,'--no-malloc-may-fail','--enforce-contract',row['contract']['contracted_function_name'],str(O/'entry.out'),str(O/'contract.out')],
 [str(B/'goto-instrument'),'--add-library','--no-malloc-may-fail',str(O/'contract.out'),str(O/'library.out')],
 [str(B/'goto-instrument'),'--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',str(O/'library.out'),str(O/'reachable.out')],
 [str(B/'goto-instrument'),'--ensure-one-backedge-per-target',str(O/'reachable.out'),str(O/'ready.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','48','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'ready.out')]
]
if havoc_inputs:
 initializer=[k for k,v in names.items() if str(v).endswith('::s126_input_bytes')]
 assert len(initializer)==1,initializer
 cmds[:1]=[
  [str(B/'goto-cc'),str(raw),str(O/'initializer-declaration.c'),'-o',str(O/'declared.out')],
  [str(B/'goto-instrument'),'--replace-calls',initializer[0]+':s126_havoc_input',str(O/'declared.out'),str(O/'replaced.out')],
  [str(B/'goto-cc'),str(O/'replaced.out'),str(O/'initializer-body.c'),str(libc),'-o',str(O/'linked.out')]]
if 'run' not in sys.argv:
 assert not O.exists();O.mkdir()
 if havoc_inputs:
  (O/'initializer-declaration.c').write_text('#include <stddef.h>\nsize_t s126_havoc_input(unsigned char *,size_t);\nsize_t (*s126_keep_initializer)(unsigned char *,size_t)=s126_havoc_input;\n')
  (O/'initializer-body.c').write_text('#include <stddef.h>\nvoid __CPROVER_havoc_slice(void *,size_t);\nsize_t s126_havoc_input(unsigned char *p,size_t n){__CPROVER_havoc_slice(p,n);return n;}\n')
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),borrowed_source_sha256=sha(H/'owned-sdk-borrowed-v1/src/lib.rs'),codegen_input_sha256=sha(pin),raw_goto_sha256=sha(raw),harness_metadata_sha256=sha(metadata),harness_metadata=row,pretty_names_sha256=sha(namePath),runner_sha256=sha(Path(__file__)),tool_pins={str(p):sha(p) for p in [B/'goto-cc',B/'goto-instrument',B/'cbmc',libc]+([O/'initializer-declaration.c',O/'initializer-body.c'] if havoc_inputs else [])},abstracted_function=scan,abstracted_pretty_name=pretty,commands=cmds,qualification=__doc__,property_scope='All reachable assertions, memory-frame checks and source safety/unwinding checks; no selection',timeout_seconds=180,retained='Reached-decoder scope, concrete native/source scan transport, decoder cut instance and later-stage/runtime/oracle joins remain explicit. Codegen and failed checks are not proof evidence.'),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Cached native/reference one-heap prefix: explicit DFCC frame, pure scan overapproximation and one180s CBMC check; no arithmetic evaluation','--','python3',__file__,tag,version,'run',*(['havoc-inputs'] if havoc_inputs else [])]))
for i,cmd in enumerate(cmds):
 with (O/('step'+str(i)+'.log')).open('w') as log:
  p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:p.wait(timeout=180)
  except subprocess.TimeoutExpired:
   os.killpg(p.pid,signal.SIGKILL);p.wait();(O/'timeout.json').write_text(json.dumps(dict(command=cmd,status='not_proved',reason='180s deadline; no cap increase'))+'\n');raise
 if i<len(cmds)-1:assert p.returncode==0,(i,p.returncode)
 else:
  rows=[]
  for item in json.loads((O/('step'+str(i)+'.log')).read_text()):rows += [{k:v for k,v in r.items() if k!='trace'} for r in item.get('result',[])]
  (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,qualification='Raw exit retained; all non-cover properties must pass, covers report FAILURE when reached.'))+'\n')
  raise SystemExit(p.returncode)
