#!/usr/bin/env python3
"""Refuse/stop only this worker's process group when external Lean is active."""
import json,os,signal,subprocess,sys,time
from pathlib import Path

def processes():
 d={}
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   stat=(p/'stat').read_text().split(') ',1)[1].split()
   d[int(p.name)]=(int(stat[1]),(p/'exe').resolve().name)
  except (OSError,RuntimeError,ValueError):pass
 return d

def external_lean(own):
 d=processes()
 def child(pid):
  seen=set()
  while pid in d and pid not in seen:
   if pid==own:return True
   seen.add(pid);pid=d[pid][0]
  return False
 return [p for p,(_,exe) in d.items() if exe=='lean' and not child(p)]

active=external_lean(os.getpid())
if active:
 print(json.dumps({'refused_external_lean':active}),flush=True);sys.exit(75)
proc=subprocess.Popen(sys.argv[1:],start_new_session=True)
while proc.poll() is None:
 active=external_lean(proc.pid)
 if active:
  print(json.dumps({'stopped_own_job_external_lean':active,'own_pid':proc.pid}),flush=True)
  os.killpg(proc.pid,signal.SIGTERM)
  try:proc.wait(timeout=2)
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
  sys.exit(75)
 time.sleep(.1)
sys.exit(proc.returncode)
