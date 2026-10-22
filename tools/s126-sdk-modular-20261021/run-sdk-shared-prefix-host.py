#!/usr/bin/env python3
"""Actual native SDK decoder-entry frame and same-allocation reference cut.
Only the exact native pure std-any is overapproximated by a read-only Boolean
return. Default mode enforces the native DFCC contract. Pointwise mode checks
explicit before/after observations instead; separated-pair mode checks the
pair without assuming a frame. Single-byte mode explicitly selects one
property and cannot establish the complete safety/frame inventory by itself.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,os,signal,re,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin')
havoc_inputs='havoc-inputs' in sys.argv
pair='separated-pair' in sys.argv
pointwise='pointwise' in sys.argv or pair
plain='plain' in sys.argv
single='single-byte' in sys.argv
if single:assert plain and pointwise
tag,version=sys.argv[1:3];P=H/('sdk-shared-prefix-'+version);O=H/tag
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=H/('sdk-shared-prefix-codegen-'+version+'-input.json');inp=json.loads(pin.read_text())
assert sha(P/'src/lib.rs')==inp['source_sha256']
assert sha(P/'Cargo.toml')==inp['cargo_sha256']
crate_name=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_')
wanted='proofs::native_owned_decoder_prefix';line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn native_owned_decoder_prefix()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_shared_prefix*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['crate_name']==crate_name and row['pretty_name']==wanted and row['original_start_line']==line and (row['attributes']['kind']=='Proof' if pointwise else row['attributes']['kind']=={'ProofForContract':{'target_fn':'native_prefix'}}):selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0];raw=Path(row['goto_file']);assert raw.is_file() and raw.name.endswith('.symtab.out')
if not pointwise:assert row['contract'] and not row['contract']['recursion_tracker']
namePath=Path(str(raw).replace('.symtab.out','.pretty_name_map.json'));names=json.loads(namePath.read_text())
scans=[(k,v) for k,v in names.items() if '::any::' in str(v) and 'u8' in str(v) and 'stage1' in k];assert len(scans)==1,scans
scan,pretty=scans[0];entries=[k for k,v in names.items() if v==wanted];assert len(entries)==1
entry=entries[0];libc=Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c')
cmds=[
 [str(B/'goto-cc'),str(raw),str(libc),'-o',str(O/'linked.out')],
 [str(B/'goto-instrument'),'--remove-function-body',scan,str(O/'linked.out'),str(O/'removed.out')],
 [str(B/'goto-instrument'),'--generate-function-body',re.escape(scan),'--generate-function-body-options','nondet-return',str(O/'removed.out'),str(O/'abstract.out')],
 [str(B/'goto-cc'),str(O/'abstract.out'),'--function',entry,'-o',str(O/'entry.out')],
 *([] if pointwise else [[str(B/'goto-instrument'),'--dfcc',entry,'--no-malloc-may-fail','--enforce-contract',row['contract']['contracted_function_name'],str(O/'entry.out'),str(O/'contract.out')]]),
 [str(B/'goto-instrument'),'--add-library','--no-malloc-may-fail',str(O/('entry.out' if pointwise else 'contract.out')),str(O/'library.out')],
 [str(B/'goto-instrument'),'--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',str(O/'library.out'),str(O/'reachable.out')],
 [str(B/'goto-instrument'),'--ensure-one-backedge-per-target',str(O/'reachable.out'),str(O/'ready.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','48','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'ready.out')]
]
if plain:cmds[-1].remove('--json-ui')
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
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),borrowed_source_sha256=sha(H/'owned-sdk-borrowed-v1/src/lib.rs'),codegen_input_sha256=sha(pin),raw_goto_sha256=sha(raw),harness_metadata_sha256=sha(metadata),harness_metadata=row,pretty_names_sha256=sha(namePath),runner_sha256=sha(Path(__file__)),tool_pins={str(p):sha(p) for p in [B/'goto-cc',B/'goto-instrument',B/'cbmc',libc]+([O/'initializer-declaration.c',O/'initializer-body.c'] if havoc_inputs else [])},abstracted_function=scan,abstracted_pretty_name=pretty,commands=cmds,qualification=('Pointwise native-prefix byte/descriptor/scalar before-after checks; no DFCC, no owned reference loaded. Same read-only std-any overapproximation. Extensional/runtime/scan/caller composition remains required.' if pointwise else __doc__),property_scope=('Only named byte-preservation assertion. All other safety/unwinding/cover/caller properties require their checked union.' if single else 'All reachable assertions and source safety/unwinding checks; no selection'),timeout_seconds=180,retained='Reached-decoder scope, concrete native/source scan transport, decoder cut instance and later-stage/runtime/oracle joins remain explicit. Codegen and failed checks are not proof evidence.'),indent=2)+'\n')
 if pair:
  p=H/(tag+'-input.json');m=json.loads(p.read_text());m['qualification']='Actual SDK native/full borrowed-reference decoder-prefix pair. No DFCC/native frame is assumed. Independent byte-frame certificates and input-heap composition are required separately; ordinary proof, no SDK method stubs.';p.write_text(json.dumps(m,indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Native prefix: '+('native/reference pair, frame certified separately' if pair else 'symbolic pointwise before/after assertions, no DFCC' if pointwise else 'explicit DFCC frame')+', pure scan overapproximation and one180s CBMC check; no arithmetic evaluation','--','python3',__file__,tag,version,'run',*(['havoc-inputs'] if havoc_inputs else []),*(['pointwise'] if pointwise else []),*(['plain'] if plain else []),*(['single-byte'] if single else []),*(['separated-pair'] if pair else [])]))
for i,cmd in enumerate(cmds):
 if plain and i==len(cmds)-1:
  invcmd=cmd.copy();invcmd[-1:-1]=['--show-properties','--json-ui']
  inventory=subprocess.run(invcmd,capture_output=True,text=True,timeout=180,check=True).stdout
  (O/'property-inventory.json').write_text(inventory)
  props=[p for item in json.loads(inventory) for p in item.get('properties',[])]
  if single:
   selected=[p for p in props if p['description']=='"arbitrary native-prefix account byte preserved"'];assert len(selected)==1
   cmd[-1:-1]=['--property',selected[0]['name']]
   (O/'property-selection.json').write_text(json.dumps(dict(command=cmd,selected_properties=selected,unselected_property_count=len(props)-1,program_sha256=sha(Path(cmd[-1])),qualification='Single allocation/byte assertion partition only; no credit for unselected safety/unwinding/caller properties.'),indent=2)+'\n')
 with (O/('step'+str(i)+'.log')).open('w') as log:
  p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:p.wait(timeout=180)
  except subprocess.TimeoutExpired:
   os.killpg(p.pid,signal.SIGKILL);p.wait();(O/'timeout.json').write_text(json.dumps(dict(command=cmd,status='not_proved',reason='180s deadline; no cap increase'))+'\n');raise
 if i<len(cmds)-1:assert p.returncode==0,(i,p.returncode)
 else:
  rows=[]
  if plain:
   expected={p['name']:p for p in props};current=None;block=[]
   for line in (O/('step'+str(i)+'.log')).read_text().splitlines():
    end=line.find('] ') if line.startswith('[') else -1
    while end>=0 and line[1:end] not in expected:end=line.find('] ',end+2)
    if end>=0:
     assert current is None,('unterminated property',current)
     current=line[1:end];block=[line[end+2:]]
    elif current is not None:block.append(line)
    if current is not None:
     m=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
     if m:rows.append(dict(property=current,description=m[1],status=m[2]));current=None;block=[]
   assert current is None
   assert len(rows)==len({r['property'] for r in rows})
   assert {r['property'] for r in rows}==({p['name'] for p in selected} if single else set(expected))
  else:
   for item in json.loads((O/('step'+str(i)+'.log')).read_text()):rows += [{k:v for k,v in r.items() if k!='trace'} for r in item.get('result',[])]
  (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,qualification='Raw exit retained; all non-cover properties must pass, covers report FAILURE when reached.'))+'\n')
  raise SystemExit(p.returncode)
