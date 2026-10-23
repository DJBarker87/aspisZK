#!/usr/bin/env python3
"""Diagnostic exception stack only, never an accepted verification result."""
from pathlib import Path
import subprocess,os,json,hashlib,sys,signal
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag='sdk-prefix-smt-exception-v1';P=H/tag;P.mkdir(exist_ok=True)
B=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');source=H/'kit/trace-cbmc-exception.cpp'
program=H/'sdk-prefix-context-check-v4/ready.out';z=H/'z3-tool-v1/bin/z3';os.environ['PATH']=str(z.parent)+':'+os.environ.get('PATH','/usr/bin:/bin')
commands=[['g++','-std=c++17','-O2','-shared','-fPIC',str(source),'-o',str(P/'exception-trace.so'),'-ldl'],[str(B),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','40','--unwindset','memcmp.0:689','--z3','--slice-formula','--unwinding-assertions','--json-ui',str(program)]]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if len(sys.argv)<2:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(qualification=__doc__,commands=commands,source_sha256=sha(source),program_sha256=sha(program),tool_pins={str(p):sha(p) for p in [B,z]},gpp_version=subprocess.check_output(['g++','--version'],text=True)),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Compile tiny optimized exception observer then locate existing SMT conversion error; diagnostic only','--','python3',__file__,'run']))
for i,cmd in enumerate(commands):
 env=dict(os.environ)
 if i:env['LD_PRELOAD']=str(P/'exception-trace.so')
 with (P/('step'+str(i)+'.log')).open('w') as output:
  child=subprocess.Popen(cmd,stdout=output,stderr=subprocess.STDOUT,env=env,start_new_session=True)
  try:child.wait(timeout=60)
  except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait();raise
 if i==0:assert child.returncode==0,child.returncode
raise SystemExit(child.returncode)
