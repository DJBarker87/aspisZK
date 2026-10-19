#!/usr/bin/env python3
"""Collect source patches/receipts and a bounded byte-exact trace excerpt."""
from pathlib import Path
import hashlib,json,subprocess

here=Path(__file__).resolve().parent;area=here.parents[1]
evidence=area/'evidence/cu-equivalence-20261019';out=evidence/'associated-types-diagnostic-a'
out.mkdir(exist_ok=False)
remote='/home/dombarker/project-offloads/aspis-r1-cu-equivalence-20261019'
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','ConnectTimeout=10']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={}
def fetch(source,destination):
    target=out/destination;target.parent.mkdir(parents=True,exist_ok=True)
    subprocess.run(['scp',*opts,host+':'+remote+'/'+source,str(target)],check=True)
    files[destination]=dict(remote_path=remote+'/'+source,sha256=sha(target),bytes=target.stat().st_size)
for file in ['associated-types.patch','build.sh','preflight.json','receipt.json','compile-time.log','compile.log','version.txt']:
    fetch('aeneas-associated-types/'+file,'build/'+file)
for name in ['array-loop-isolated-a','array-loop-borrow-diagnostic-b','array-loop-associated-types-a']:
    for file in ['projection.json','command.json']:fetch(name+'/'+file,name+'/'+file)
subprocess.run(['scp',*opts,'-r',host+':'+remote+'/associated-types-regression-a',str(out/'regression')],check=True)
for p in (out/'regression').rglob('*'):
    if p.is_file():
        key=str(p.relative_to(out));files[key]=dict(sha256=sha(p),bytes=p.stat().st_size)
trace=evidence/'array-deref-loop-trace-a/stdout.log'
raw=trace.read_bytes();marker=b'Joined contexts:';first=raw.rindex(marker)
last=raw.index(b'Compiler source:',first)
excerpt=out/'loop-contexts-excerpt.log';excerpt.write_bytes(raw[first:last])
files[excerpt.name]=dict(sha256=sha(excerpt),bytes=excerpt.stat().st_size,
    full_trace_sha256=sha(trace),full_trace_bytes=len(raw),first_byte=first,last_byte=last,
    full_remote_path=remote+'/runs/array-deref-loop-trace-a/stdout.log')
manifest=dict(status='LOOP_BORROW_CHECK_FIXED_FULL_LIBRARY_ADMISSION_OPEN',files=files,
    notes=['No iteration limit was increased.',
      'Existing pinned frontends remain untouched.',
      'Only exact physically identical associated types containing no regions take the opt-in new match case.',
      'Full library emission remains failed due to generic Try/Residual typing/dictionary support.',
      'LLBC dereference normalization remains experimental and requires semantic admission.',
      'Partial generated declarations with unresolved identifiers are not imported.'])
(out/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Keep the full large trace in ignored local scratch and at its hashed remote path.
scratch=area.parents[2]/'.cu-local-proof/associated-types'
scratch.mkdir(parents=True,exist_ok=True)
target=scratch/'loop-trace-a.log';assert not target.exists();trace.rename(target)
print(json.dumps(dict(status=manifest['status'],files=len(files),trace_excerpt_bytes=excerpt.stat().st_size)))
