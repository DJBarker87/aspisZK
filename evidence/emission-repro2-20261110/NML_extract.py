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
for old,new in [('NHR_STAGING_MANIFEST.json','NML_STAGING_MANIFEST.json'),('NHR_FROZEN_PAYLOAD.json.xz','NML_FROZEN_PAYLOAD.json.xz'),('NHR_FROZEN_PAYLOAD.json.sha256','NML_FROZEN_PAYLOAD.json.sha256')]:
 p=E/old
 if not p.exists():p.symlink_to(new)
 assert p.resolve()==(E/new).resolve()
p=E/'NML_NHR_stage.py';assert hashlib.sha256(p.read_bytes()).hexdigest()==json.loads((E/'NML_STAGER_PIN.json').read_text())['sha256']
loader=importlib.util.spec_from_file_location('NML_private_NHR_stage',p);m=importlib.util.module_from_spec(loader);loader.loader.exec_module(m)
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
 entry=dict(attempt=run,tool=tool,command=cmd,started_unix=time.time(),source_revision=json.loads((E/(run+'.json')).read_text())['source_revision'],frozen_validation_revision=m.REV,archive_source_git_blob=spec['configuration']['source']['git_blob'],tool_sha256=hashlib.sha256(Path(cmd[0]).read_bytes()).hexdigest(),archive_source_sha256=spec['reference_sha256'],archive_manifest_sha256=spec['manifest_sha256'])
 with (E/'NML_TOOL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n');f.flush();os.fsync(f.fileno())
 r=original_run(['/usr/bin/time','-v','-o',str(out/(tool+'.time'))]+cmd,*a,**kw)
 entry.update(exit=r.returncode,wall_seconds=time.time()-entry['started_unix'],time_receipt=str(out/(tool+'.time')))
 (out/(tool+'_receipt.json')).write_text(json.dumps(entry,indent=2)+'\n')
 return r
subprocess.run=measured
import types
args=types.SimpleNamespace(function='repro',cargo='/home/dombarker/.cargo/bin/cargo')
ref=E/spec['reference_directory'];source=ref/spec.get('source_relative','src/lib.rs');manifest=ref/'Cargo.toml'
for extra in spec.get('package_extras',[]):assert hashlib.sha256((ref/extra['relative_path']).read_bytes()).hexdigest()==extra['sha256']
assert hashlib.sha256(source.read_bytes()).hexdigest()==spec['reference_sha256']
assert hashlib.sha256(manifest.read_bytes()).hexdigest()==spec['manifest_sha256']
try:
 status=m.extract(args,E/'NML_workspace',out)
finally:
 for extra in spec.get('package_extras',[]):assert hashlib.sha256((ref/extra['relative_path']).read_bytes()).hexdigest()==extra['sha256'],'STOP archived package input drift'
 assert hashlib.sha256(source.read_bytes()).hexdigest()==spec['reference_sha256'],'STOP archive input drift'
 assert hashlib.sha256(manifest.read_bytes()).hexdigest()==spec['manifest_sha256'],'STOP archive manifest drift'
 lock=ref/'Cargo.lock'
 (out/'NML_REFERENCE_POSTCHECK.json').write_text(json.dumps(dict(source_sha256=spec['reference_sha256'],manifest_sha256=spec['manifest_sha256'],reference_basis=spec['reference_basis'],manifest_basis=spec['manifest_basis'],reference_lock_sha256=hashlib.sha256(lock.read_bytes()).hexdigest() if lock.exists() else None,reference_lock_note='Historical standalone std-only crate; no frozen-release dependency is substituted. Frozen release Cargo.lock independently checked by NHR_stage.',source_revision=json.loads((E/(run+'.json')).read_text())['source_revision']),indent=2))
print(json.dumps(dict(attempt=run,exit=status)),flush=True)
sys.exit(status)
