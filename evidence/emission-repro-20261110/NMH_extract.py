#!/usr/bin/env python3
"""Apply archived options through the unchanged, hash-pinned NHR extractor.
Only options() is supplied by this owned controller; stage/validate/extract and
all source/lock/tool/opacity checks are the original NHR implementation.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util,json,hashlib,subprocess,time,os
E=Path(__file__).resolve().parent
spec=json.loads((E/(sys.argv[1]+'_spec.json')).read_text());run=spec['run']
for old,new in [('NHR_STAGING_MANIFEST.json','NMH_STAGING_MANIFEST.json'),('NHR_FROZEN_PAYLOAD.json.xz','NMH_FROZEN_PAYLOAD.json.xz'),('NHR_FROZEN_PAYLOAD.json.sha256','NMH_FROZEN_PAYLOAD.json.sha256')]:
 p=E/old
 if not p.exists():p.symlink_to(new)
 assert p.resolve()==(E/new).resolve()
p=E/'NMH_NHR_stage.py';assert hashlib.sha256(p.read_bytes()).hexdigest()==json.loads((E/'NMH_STAGER_PIN.json').read_text())['sha256']
loader=importlib.util.spec_from_file_location('NMH_private_NHR_stage',p);m=importlib.util.module_from_spec(loader);loader.loader.exec_module(m)
# Independently enforce the exact capped context even though extract() is called as API.
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
cg=Path('/sys/fs/cgroup')/rel
assert {n:(cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max','pids.max')}=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
out=E/(run+'_emitted');out.mkdir(exist_ok=True)
m.options=lambda args,workspace,out:dict(charon_command=spec['charon_command'],aeneas_command=spec['aeneas_command'],opacity=spec['opacity'],root=spec['configuration']['roots'])
original_run=subprocess.run
# Record distinct tool invocations, exact argv and GNU time metrics, even on failure.
def measured(cmd,*a,**kw):
 tool=next((k for k in ['charon','aeneas'] if cmd[0]==spec[k+'_command'][0]),None)
 if not tool:return original_run(cmd,*a,**kw)
 entry=dict(attempt=run,tool=tool,command=cmd,started_unix=time.time(),source_revision=m.REV,tool_sha256=hashlib.sha256(Path(cmd[0]).read_bytes()).hexdigest())
 with (E/'NMH_TOOL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n');f.flush();os.fsync(f.fileno())
 r=original_run(['/usr/bin/time','-v','-o',str(out/(tool+'.time'))]+cmd,*a,**kw)
 entry.update(exit=r.returncode,wall_seconds=time.time()-entry['started_unix'],time_receipt=str(out/(tool+'.time')))
 (out/(tool+'_receipt.json')).write_text(json.dumps(entry,indent=2)+'\n')
 return r
subprocess.run=measured
import types
args=types.SimpleNamespace(function='repro',cargo='/home/dombarker/.cargo/bin/cargo')
status=m.extract(args,E/'NMH_workspace',out)
print(json.dumps(dict(attempt=run,exit=status)),flush=True)
sys.exit(status)
