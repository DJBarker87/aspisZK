#!/usr/bin/env python3
"""Collect text receipts and hashes only; never copy LLBC or executable artifacts."""
import json, pathlib, subprocess
HERE=pathlib.Path(__file__).resolve().parent
script=r'''
import hashlib,json,pathlib,re
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021')
E=R/'continuation3'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
kani={}
for d in E.iterdir():
    if not (d/'receipt.json').exists():continue
    x=json.loads((d/'receipt.json').read_text())
    out=(d/'stdout.log').read_text();err=(d/'stderr.log').read_text()
    x.update(stdout_sha256=sha(d/'stdout.log'),stderr_sha256=sha(d/'stderr.log'),
      result=out[out.rfind('Thread 0: Checking harness'):] if 'Thread 0: Checking harness' in out else out[-5000:],
      compiler_errors=[l for l in (out+err).splitlines() if 'error:' in l],time_log=(d/'time.log').read_text())
    if x['exit_status']==124:
        x['peak_rss_kib_incomplete_parent_only']=x.pop('peak_rss_kib')
        x['whole_job_process_peak_rss_kib']=None
        x['status']='TIMEOUT, no verdict; cgroup memory peak is the aggregate measurement'
    if (d/'source-pins.json').exists():x['source_pins']=json.loads((d/'source-pins.json').read_text())
    kani[d.name]=x
extract={}
for d in sorted(E.glob('extract-*')):
    x={}
    for f in ['charon.log','charon-time.log','aeneas.log','aeneas-time.log']:
        if (d/f).exists():
            data=(d/f).read_text();x[f]=dict(sha256=sha(d/f),size=(d/f).stat().st_size,
              text=data if f.endswith('time.log') else '\n'.join(data.splitlines()[-85:]))
    for f in ['reference.llbc','generated/Reference.lean']:
        if (d/f).exists():x[f]=dict(sha256=sha(d/f),size=(d/f).stat().st_size)
    extract[d.name]=x
tools={}
for p in [pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'),
          pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas'),
          pathlib.Path('/home/dombarker/.cargo/bin/cargo-kani'),
          pathlib.Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),
          pathlib.Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]:
    tools[str(p)]=dict(sha256=sha(p),size=p.stat().st_size)
print(json.dumps(dict(kani=kani,extractions=extract,tools=tools,
    reservation_waits=(E/'reservation-waits.jsonl').read_text() if (E/'reservation-waits.jsonl').exists() else '',
    early_success_source_pins=json.loads((E/'raw-and-relational-source-pins.json').read_text()))))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True,capture_output=True,check=True)
data=json.loads(r.stdout)
e=HERE/'builder-cont3-evidence'
(e/'kani-and-extraction.json').write_text(json.dumps(data,indent=2)+'\n')
print('collected',len(data['kani']),'Kani receipts,',len(data['extractions']),'extraction directories')
