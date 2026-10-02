#!/usr/bin/env python3
"""Read-only NUC hash inventory for the R391 source and cached object inputs."""
import json, pathlib, subprocess, hashlib
here=pathlib.Path(__file__).resolve().parent
remote=r'''python3 - <<'PY2'
from pathlib import Path
import hashlib, json
src=Path('/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a')
cache=Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib')
rows={}
for name,rel in [('R161WrappedMulExecution','AspisV8R19/R161WrappedMulExecution.lean'),('R156FunsCore','AspisR156FullFreeze/FunsCore.lean')]:
 s=src/rel;o=cache/rel.replace('.lean','.olean')
 rows[name]={'source_path':str(s),'source_exists':s.is_file(),'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest(),'olean_path':str(o),'olean_exists':o.is_file(),'olean_sha256':hashlib.sha256(o.read_bytes()).hexdigest(),'olean_size':o.stat().st_size}
a=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean/Aeneas/Std.olean')
rows['AeneasStd']={'path':str(a),'exists':a.is_file(),'sha256':hashlib.sha256(a.read_bytes()).hexdigest()}
print(json.dumps(rows,indent=2))
PY2'''
proc=subprocess.run(['ssh','-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null','dombarker@100.108.41.90',remote],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
(here/'source-cache-audit.nuc.json').write_text(proc.stdout)
(here/'source-cache-audit.ssh-stderr.txt').write_text(proc.stderr)
data=json.loads(proc.stdout)
for name, rel in [('R161WrappedMulExecution','provenance/lean-dependencies/AspisV8R19/R161WrappedMulExecution.lean'),('R156FunsCore','provenance/lean-dependencies/AspisR156FullFreeze/FunsCore.lean')]:
 local=here/rel; localhash=hashlib.sha256(local.read_bytes()).hexdigest()
 assert localhash==data[name]['source_sha256'],(name,localhash,data[name]['source_sha256'])
 data[name]['portable_copy_path']=str(local.relative_to(here)); data[name]['portable_copy_sha256']=localhash
# Historical receipts recorded only R388.Funs direct scratch source, not R161 source/object; no receipt rewritten.
(data.__class__ if False else None)
report={'status':'read-only R391 NUC source/cache identity audit','pinned_source_root':'/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','pinned_cache_root':'/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib','remote_records':data,'historical_receipt_basis':{'successful_run_id':'1790957475592362000','receipt':' .r21-scratch/aspis-focus-1790957475592362000.receipt.json'.strip(),'receipt_sha256':hashlib.sha256((here/'.r21-scratch/aspis-focus-1790957475592362000.receipt.json').read_bytes()).hexdigest(),'direct_local_import_map':json.loads((here/'.r21-scratch/aspis-focus-1790957475592362000.receipt.json').read_text())['direct_local_import_sha256'],'note':'The original receipt remains unchanged and did not include R161WrappedMulExecution in its direct-local-source map; this separate audit binds the copied source to the pinned NUC source and records actual pinned cache object hashes/paths.'}}
(here/'source-cache-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print('R391 NUC source/cache audit: PASS')
