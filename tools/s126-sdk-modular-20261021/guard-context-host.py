#!/usr/bin/env python3
"""Parent-only diagnostic under an explicit pure-scan overapproximation.

NOT a full source proof by itself. The dropped callee checks/frame and exact
bool must be supplied by the SDK next-step and emitted-loop certificates.
All real AccountInfo/borrow/caller code and other assertions remain present.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');B=Path('/home/dombarker/.kani/kani-0.67.0/bin');mode=os.environ.get('S126_CONTEXT_MODE','prefix');assert mode in ['prefix','full','alias','clean'];name='sdk-guard-context-v1' if mode=='prefix' else 'sdk-'+mode+'-guard-context-'+('v2' if mode in ['full','alias'] else 'v1');O=H/name;O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pattern='aspis_s126_sdk_'+mode+'_context_v1*pretty_name_map.json' if mode!='prefix' else 'aspis_s126_sdk_prefix_boundary_v7*pretty_name_map.json'
files=list((H/'target/kani').rglob(pattern));assert len(files)==1,files
names=json.loads(files[0].read_text());selected=[(k,v) for k,v in names.items() if '::any::' in str(v) and "u8" in str(v) and 'stage1' in str(k)]
if len(selected)!=1:
 print([(k,v) for k,v in names.items() if '::any' in str(v)][:10])
 raise SystemExit('Exact scan symbol not selected; no solver launched.')
fn,pretty=selected[0];source=Path(str(files[0]).replace('.pretty_name_map.json','.out'));assert source.is_file()
commands=[
 [str(B/'goto-instrument'),'--remove-function-body',fn,str(source),str(O/'removed.out')],
 [str(B/'goto-instrument'),'--generate-function-body',re.escape(fn),'--generate-function-body-options','nondet-return',str(O/'removed.out'),str(O/'abstract.out')],
 [str(B/'cbmc'),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','1772','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--json-ui',str(O/'abstract.out')]
]
if mode!='prefix':
 entries=[k for k,v in names.items() if v=='proofs::actual_sdk_stage1_'+mode+'_context'];assert len(entries)==1,entries
 commands[2][1:1]=['--function',entries[0]]
 if mode=='alias':commands[2][commands[2].index('--unwind')+1]='36'
if len(sys.argv)==1:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(name+'-input.json')).write_text(json.dumps(dict(commands=commands,input_goto_sha256=sha(source),pretty_names_sha256=sha(files[0]),abstracted_function=fn,pretty_name=pretty,tool_pins={str(p):sha(p) for p in [B/'goto-instrument',B/'cbmc']},qualification=__doc__),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),'Parent-only actual SDK context with one explicitly abstracted pure guard; no whole-source claim','--','python3',__file__,'run']))
for i,cmd in enumerate(commands):
 with (O/('step'+str(i)+'.log')).open('w') as out:
  p=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT,timeout=180)
 if i<2 and p.returncode!=0:raise SystemExit(p.returncode)
 if i==2:
  (O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,qualification='Raw CBMC exit retained; covers are assertion counterexamples and must be classified explicitly. This script does not convert a failing proof into exit0.'))+'\n')
  raise SystemExit(p.returncode)
