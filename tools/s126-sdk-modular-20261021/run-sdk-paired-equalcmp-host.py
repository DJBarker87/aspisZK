#!/usr/bin/env python3
"""Diagnostic paired source context with asserted specialized equal688 memcmp.
The original frozen Rust stage1 and full borrowed SDK reference remain intact.
All specialization requirements are caller assertions, never assumptions.
The same-start/distinct-object zero-return/read-only leaf is separately checked;
full array-intrinsic/heap/caller transport still needs an explicit audit.
"""
from pathlib import Path
import os,sys,json,hashlib,subprocess,signal,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin');tag=sys.argv[1];O=H/tag
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
version='v10' if 'ghost' in sys.argv else 'v9'
P=H/('sdk-paired-context-'+version);pin=H/('sdk-paired-context-codegen-'+version+'-input.json');old=json.loads(pin.read_text());assert old['source_sha256']==sha(P/'src/lib.rs')
wanted='proofs::paired_parent_context';line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn paired_parent_context()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_paired_context_v1*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']==wanted and row['original_start_line']==line and row['attributes'].get('verified_stubs'):selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0];raw=Path(row['goto_file']);assert raw.is_file()
namesPath=Path(str(raw).replace('.symtab.out','.pretty_name_map.json'));names=json.loads(namesPath.read_text())
assert names.get('memcmp')=='memcmp';entry=[n for n,v in names.items() if v==wanted];assert len(entry)==1
scan=[n for n,v in names.items() if '::any::' in str(v) and 'u8' in str(v) and 'stage1' in n];assert len(scan)==1,scan
libc=Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c');decl=H/'kit/memcmp688-declaration.c';body=H/'kit/memcmp688-equal.c'
commands=[
 [str(B/'goto-cc'),str(raw),str(libc),str(decl),'-o',str(O/'declared.out')],
 [str(B/'goto-instrument'),'--replace-calls','memcmp:s126_memcmp688_equal',str(O/'declared.out'),str(O/'replaced.out')],
 [str(B/'goto-cc'),str(O/'replaced.out'),str(body),'-o',str(O/'appended.out')],
 [str(B/'goto-cc'),str(O/'appended.out'),'--function',entry[0],'-o',str(O/'entry.out')],
 [str(B/'goto-instrument'),'--remove-function-body',scan[0],str(O/'entry.out'),str(O/'scanremoved.out')],
 [str(B/'goto-instrument'),'--generate-function-body',re.escape(scan[0]),'--generate-function-body-options','nondet-return',str(O/'scanremoved.out'),str(O/'scan.out')],
 [str(B/'goto-instrument'),'--add-library','--no-malloc-may-fail',str(O/'scan.out'),str(O/'library.out')],
 [str(B/'goto-instrument'),'--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',str(O/'library.out'),str(O/'reachable.out')],
 [str(B/'goto-instrument'),'--ensure-one-backedge-per-target',str(O/'reachable.out'),str(O/'ready.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','40','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'ready.out')]
]
if 'run' not in sys.argv:
 assert not O.exists();O.mkdir()
 for source in [Path(__file__),decl,body]:
  (O/source.name).write_bytes(source.read_bytes())
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),reused_compile_input_sha256=sha(pin),raw_goto_sha256=sha(raw),harness_metadata_sha256=sha(metadata),harness_metadata=row,pretty_names_sha256=sha(namesPath),runner_sha256=sha(Path(__file__)),tool_pins={str(p):sha(p) for p in [B/'goto-cc',B/'goto-instrument',B/'cbmc',libc,decl,body]},commands=commands,leaf_receipt_sha256=sha(H/'receipts/memcmp-equal-join-v1/receipt.json'),native_scan_overapproximation=scan[0],property_scope='All source safety and caller assertions, all C-specialization requirements ASSERTED, full unwinding checks. No property selection.',qualification=__doc__,timeout_seconds=180),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Raw exact paired caller codegen with asserted equal688 memcmp specialization: normal linking, one named scan overapproximation, at most180s all-properties CBMC','--','python3',__file__,tag,'run',*(['ghost'] if version=='v10' else [])]))
for i,cmd in enumerate(commands):
 with (O/('step'+str(i)+'.log')).open('w') as log:
  process=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:process.wait(timeout=180)
  except subprocess.TimeoutExpired:
   os.killpg(process.pid,signal.SIGKILL);process.wait();(O/'timeout.json').write_text(json.dumps(dict(command=cmd,status='not_proved',reason='180s timeout; no cap increase'))+'\n');raise
 if i<len(commands)-1:assert process.returncode==0,process.returncode
 else:
  rows=[]
  try:
   for item in json.loads((O/('step'+str(i)+'.log')).read_text()):rows += [{k:v for k,v in p.items() if k!='trace'} for p in item.get('result',[])]
   (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
  except (ValueError,TypeError):pass
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=process.returncode,qualification='Raw exit retained; covers reach via FAILURE, every non-cover must SUCCESS.'))+'\n')
  raise SystemExit(process.returncode)
