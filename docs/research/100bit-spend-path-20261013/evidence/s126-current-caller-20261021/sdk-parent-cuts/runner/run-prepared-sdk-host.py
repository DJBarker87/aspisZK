#!/usr/bin/env python3
"""Reuse a pinned prepared caller GOTO; change only the SMT encoding profile.
No Rust/SDK/carrier change. Retain every check and inherited source cut.
"""
from pathlib import Path
import sys,subprocess,hashlib,json,os,signal
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag,previous=sys.argv[1:3]
O=H/tag;O.mkdir(exist_ok=True);prior=H/(previous+'-input.json');base=json.loads(prior.read_text())
receipt=H/'receipts'/previous/'receipt.json';r=json.loads(receipt.read_text())
refs=[a.split('=',1)[1] for a in r['command'] if a.startswith('reuse-codegen=')];assert len(refs)==1
codegen=Path(refs[0]);c=json.loads(codegen.read_text());source=Path(c['command'][c['command'].index('--manifest-path')+1]).parent/'src/lib.rs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(codegen)==base['artifact_selection']['codegen_input_sha256']
assert sha(source)==c['source_sha256']==base['artifact_selection']['source_sha256']
cmd=list(base['commands'][-1]);assert '--z3' in cmd and '--sat-solver' not in cmd
program=Path(cmd[-1]);assert program.is_file() and program.parent==H/previous
z=H/'z3-tool-v1/bin/z3';pos=cmd.index('--z3');cmd[pos:pos+1]=['--bitwuzla','--external-smt2-solver',str(z)]
os.environ['PATH']=str(z.parent)+':'+os.environ.get('PATH','/usr/bin:/bin')
if len(sys.argv)<4:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(source),codegen_input_sha256=sha(codegen),prior_input_sha256=sha(prior),prior_receipt_sha256=sha(receipt),program_sha256=sha(program),tool_pins={str(p):sha(p) for p in [Path(cmd[0]),z]},runner_sha256=sha(Path(__file__)),qualification=__doc__,solver='Actual Z3 4.15.4 via CBMC Bitwuzla SMT-LIB encoding profile: flat structs, SMT arrays, no datatype map lookup. All inherited safety/unwinding checks retained.',inherited_cut=base.get('qualification')),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Reuse cached exact caller; SMT flat-structure conversion and bounded solver, no compilation','--','python3',__file__,tag,previous,'run']))
pin=json.loads((H/(tag+'-input.json')).read_text());assert sha(program)==pin['program_sha256']
with (O/'cbmc.log').open('w') as output:
 child=subprocess.Popen(cmd,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
 try:child.wait(timeout=180)
 except subprocess.TimeoutExpired:
  os.killpg(child.pid,signal.SIGKILL);child.wait();(O/'timeout.json').write_text(json.dumps(dict(timeout_seconds=180,qualification='No proof completion.'))+'\n');raise
assert sha(program)==pin['program_sha256']
try:
 items=json.loads((O/'cbmc.log').read_text());rows=[{k:v for k,v in row.items() if k!='trace'} for item in items for row in item.get('result',[])]
 (O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
except ValueError:pass
raise SystemExit(child.returncode)
