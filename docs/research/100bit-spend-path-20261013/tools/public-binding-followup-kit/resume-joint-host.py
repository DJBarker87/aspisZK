#!/usr/bin/env python3
"""Reuse one in-memory verified import snapshot only across external interruptions."""
from pathlib import Path
from types import SimpleNamespace
import hashlib,importlib.util,json,sys
W=Path('/home/dombarker/project-offloads/aspis-r1-public-binding-joint-c16-20261016')
spec=importlib.util.spec_from_file_location('focused',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
original_verify=r.verify_snapshot;cached=None;guard=r.external_lean;interrupted=False

def once(path):
 global cached
 if cached is None:cached=original_verify(path)
 else:
  for p,stat in cached[1].items():
   current=Path(p).stat();assert (current.st_size,current.st_mtime_ns)==stat,('Pinned external changed',p)
 return cached

def observed(own=None):
 global interrupted
 found=guard(own)
 if own is not None and found:interrupted=True
 return found

r.verify_snapshot=once;r.external_lean=observed
manifest=r.staged(W);records=[]
for i in range(1,5):
 interrupted=False
 args=SimpleNamespace(workspace=W,target=['ExtractedFirstCallerReachability'],group=None,external_snapshot=W/'external-inputs.json',attempt='joint-resume-'+str(i),revision='162f2a4d0+shared-c16ab4d76-current-caller-universe')
 status=r.run(args,manifest)
 records.append({'attempt':args.attempt,'status':status,'external_interruption':interrupted,'full_snapshot_verified_once_in_memory':True,'per_target_stat_identity_checks_retained':True})
 (W/'resume-record.json').write_text(json.dumps({'attempts':records,'external_snapshot_sha256':hashlib.sha256((W/'external-inputs.json').read_bytes()).hexdigest(),'policy':'Only interrupted own Lean may retry; hashes verified once in memory, all pinned external stat identities rechecked and own source/object producing keys verified by unchanged runner every target.'},indent=2)+'\n')
 if status==0:sys.exit(0)
 if not interrupted:sys.exit(status)
sys.exit(75)
