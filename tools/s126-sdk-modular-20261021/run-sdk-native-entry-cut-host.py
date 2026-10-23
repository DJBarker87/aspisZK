#!/usr/bin/env python3
"""Actual SDK pre-comparison source entry with an explicit688-byte cut.
Only688-byte memcmp calls mark entry and return nonzero. All other lengths use
the original libc model. This proves upstream slot/descriptor conditions at
callee entry, not comparison equivalence or a full returned-stage theorem.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,signal,re,os
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin')
havoc_inputs='havoc-inputs' in sys.argv
first_link='first-link' in sys.argv or havoc_inputs
tag=sys.argv[1];O=H/tag;P=H/('sdk-native-context-v16' if havoc_inputs else 'sdk-native-context-v14' if first_link else 'sdk-native-context-v13');pin=H/('sdk-native-context-codegen-v20-input.json' if havoc_inputs else 'sdk-native-context-codegen-v18-input.json' if first_link else 'sdk-native-context-codegen-v17-input.json');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads(pin.read_text())['source_sha256']==sha(P/'src/lib.rs')
line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn native_parent_arguments()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_native_context_v1*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']=='proofs::native_parent_arguments' and row['original_start_line']==line and row['attributes'].get('verified_stubs'):selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0];raw=Path(row['goto_file']);prepared=Path(str(raw).replace('.symtab.out','.out'));namePath=Path(str(raw).replace('.symtab.out','.pretty_name_map.json'));names=json.loads(namePath.read_text())
marker=[k for k,v in names.items() if 's126_prefix_hits' in str(v) and not k.startswith('tag-')];assert len(marker)==1,marker
marker=marker[0];assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',marker),marker
entry=[k for k,v in names.items() if v=='proofs::native_parent_arguments'];assert len(entry)==1
scans=[k for k,v in names.items() if '::any::' in str(v) and 'u8' in str(v) and 'stage1' in k];assert len(scans)==1
libc=Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c')
cmds=[
 [str(B/'goto-cc'),str(prepared),str(O/'entry-cut-declaration.c'),'-o',str(O/'declared.out')],
 [str(B/'goto-instrument'),'--replace-calls','memcmp:s126_entry_memcmp',str(O/'declared.out'),str(O/'replaced.out')],
 [str(B/'goto-cc'),str(O/'replaced.out'),str(O/'entry-cut-body.c'),str(libc),'-o',str(O/'linked.out')],
 [str(B/'goto-cc'),str(O/'linked.out'),'--function',entry[0],'-o',str(O/'entry.out')],
 [str(B/'goto-instrument'),'--remove-function-body',scans[0],str(O/'entry.out'),str(O/'removed.out')],
 [str(B/'goto-instrument'),'--generate-function-body',re.escape(scans[0]),'--generate-function-body-options','nondet-return',str(O/'removed.out'),str(O/'abstract.out')],
 [str(B/'goto-instrument'),'--add-library','--no-malloc-may-fail',str(O/'abstract.out'),str(O/'library.out')],
 [str(B/'goto-instrument'),'--generate-function-body-options','assert-false-assume-false','--generate-function-body','.*','--drop-unused-functions',str(O/'library.out'),str(O/'reachable.out')],
 [str(B/'goto-instrument'),'--ensure-one-backedge-per-target',str(O/'reachable.out'),str(O/'ready.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','48','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'ready.out')]
]
if first_link:
 cmds.insert(4,[str(B/'goto-instrument'),'--generate-function-body','^s126_cmp_choice$','--generate-function-body-options','nondet-return',str(O/'entry.out'),str(O/'choice.out')])
 cmds[5][-2]=str(O/'choice.out')
if havoc_inputs:
 initializer=[k for k,v in names.items() if str(v).endswith('::s126_input_bytes')]
 assert len(initializer)==1,initializer
 cmds[1][1:1]=['--replace-calls',initializer[0]+':s126_havoc_input']
if 'run' not in sys.argv:
 assert not O.exists();O.mkdir()
 (O/'entry-cut-declaration.c').write_text('#include <stddef.h>\nint s126_entry_memcmp(const void *,const void *,size_t);\nint (*s126_keep_entry_declaration)(const void *,const void *,size_t)=s126_entry_memcmp;\n')
 (O/'entry-cut-body.c').write_text('#include <stddef.h>\nextern size_t '+marker+';\nint memcmp(const void *,const void *,size_t);\nint s126_entry_memcmp(const void *a,const void *b,size_t n){\n if(n==688){'+marker+'+=1;return 1;}\n return memcmp(a,b,n);\n}\n')
 if havoc_inputs:
  with (O/'entry-cut-declaration.c').open('a') as f:f.write('size_t s126_havoc_input(unsigned char *,size_t);\nsize_t (*s126_keep_initializer)(unsigned char *,size_t)=s126_havoc_input;\n')
 if first_link:
  p=O/'entry-cut-body.c';s=p.read_text().replace('int memcmp(', 'int s126_cmp_choice(void);\nint memcmp(',1).replace('+=1;return 1;}', '+=1;return s126_cmp_choice();}');p.write_text(s)
 if havoc_inputs:
  with (O/'entry-cut-body.c').open('a') as f:f.write('void __CPROVER_havoc_slice(void *,size_t);\nsize_t s126_havoc_input(unsigned char *p,size_t n){__CPROVER_havoc_slice(p,n);return n; }\n')
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),codegen_input_sha256=sha(pin),prepared_goto_sha256=sha(prepared),harness_metadata_sha256=sha(metadata),harness_metadata=row,pretty_names_sha256=sha(namePath),marker_symbol=marker,scan_overapproximation=scans[0],runner_sha256=sha(Path(__file__)),tool_pins={str(p):sha(p) for p in [B/'goto-cc',B/'goto-instrument',B/'cbmc',libc,O/'entry-cut-declaration.c',O/'entry-cut-body.c']},commands=cmds,qualification=__doc__+(' This successor uses arbitrary read-only comparison replies and also verifies the original first-entry linkage; no688-byte comparison is executed or assumed.' if first_link else ''),property_scope='All reachable source assertions and safety/unwinding checks; no property selection',timeout_seconds=180,retained='Comparison-body and later-source transport require the independently checked native guard/reference instance; marker cut itself does not execute or validate the688-byte comparison. Fixed root lengths, common typed child replies, native scan overapproximation, runtime heap embedding, ordered global correspondence remain explicit.'),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Cached native pre-comparison SDK normalization cut; other libc comparisons unchanged, then one180s all-properties CBMC check','--','python3',__file__,tag,'run',*(['havoc-inputs'] if havoc_inputs else ['first-link'] if first_link else [])]))
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
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,qualification='Raw exit retained; reached covers report FAILURE, every non-cover must pass.'))+'\n')
  raise SystemExit(p.returncode)
