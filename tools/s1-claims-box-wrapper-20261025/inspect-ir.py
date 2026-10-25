#!/usr/bin/env python3
"""Bounded read-only textual GOTO inspection; never interprets it as a proof."""
from pathlib import Path
import subprocess,hashlib,json,time,signal,os
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-claims-box-wrapper-ir-v3';P.mkdir(exist_ok=False)
w=Path('/private/tmp/s126-kani-local-diagnostic-20261025-v1');fs=list((w/'target/kani/aarch64-apple-darwin/debug/deps').glob('*box_projection_transfer.out'));assert len(fs)==1;src=fs[0];tool=w/'kani-0.67.0/bin/goto-instrument';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins={str(x):sha(x)for x in [src,tool,Path(__file__)]};cmd=[str(tool),'--show-goto-functions',str(src)];(P/'input.json').write_text(json.dumps(dict(command=cmd,pins=pins,source_receipt='s1-claims-box-wrapper-v1',kind='READ_ONLY_TEXT_IR; not a source-semantic equivalence proof',sampled_aggregate_limit_bytes=2*1024**3,output_limit_bytes=8*1024**2,timeout_seconds=20),indent=2)+'\n');start=time.monotonic();stop=None;peak=0
with (P/'functions.txt').open('wb')as out,(P/'time.log').open('wb')as err:
 child=subprocess.Popen(['/usr/bin/time','-l',*cmd],stdout=out,stderr=err,start_new_session=True)
 while child.poll() is None:
  ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
  members=[list(map(int,x.split())) for x in ps.splitlines()if len(x.split())==3];members=[x for x in members if x[1]==child.pid];rss=sum(x[2]for x in members)*1024;peak=max(peak,rss)
  if rss>2*1024**3:stop='RSS watchdog'
  elif len(members)>64:stop='process watchdog'
  elif time.monotonic()-start>20:stop='time watchdog'
  elif (P/'functions.txt').stat().st_size>8*1024**2:stop='output watchdog'
  if stop:
   os.killpg(child.pid,signal.SIGTERM)
   try:child.wait(timeout=2)
   except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL)
   break
  time.sleep(0.1)
 status=child.wait()
receipt=dict(exit_status=status,wall_seconds=time.monotonic()-start,sampled_aggregate_peak_bytes=peak,watchdog_stop=stop,stdout_bytes=(P/'functions.txt').stat().st_size,source_and_tool_unchanged=all(sha(Path(p))==h for p,h in pins.items()),print_axioms='N/A: read-only native IR inspection');(P/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
