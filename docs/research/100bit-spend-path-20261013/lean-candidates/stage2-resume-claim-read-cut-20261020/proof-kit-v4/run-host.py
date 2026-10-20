#!/usr/bin/env python3
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time
W=Path(__file__).resolve().parent
C=json.loads((W/'config.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
G=Path('/home/dombarker/project-offloads/stage2-resume-claim-read-proof-v4-kit')
SRC=G/'proof-input'
OUT=G/'attempt'
OBJ=OUT/'objects'
OUT.mkdir(exist_ok=True); (OBJ/'AspisR1Stage2ResumeSuffix').mkdir(parents=True,exist_ok=True)
cgline=Path('/proc/self/cgroup').read_text().strip(); cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':str(512*2**20),'memory.max':str(2*2**30),'memory.swap.max':'0'},limits
prefix=Path(C['prefix_objects'])
reader=Path(C['reader_success_objects'])
reader_types=Path(C['reader_types_objects'])
leanpath=[str(OBJ),str(prefix),str(reader_types),str(reader),*C['lean_path']]
env=dict(os.environ);env['LEAN_PATH']=':'.join(leanpath)
lean=Path(C['lean']);assert sha(lean)==C['lean_sha256']
steps=[('types',SRC/'AspisR1Stage2ResumeSuffix/Types.lean',OBJ/'AspisR1Stage2ResumeSuffix/Types.olean'),('external',SRC/'AspisR1Stage2ResumeSuffix/FunsExternal.lean',OBJ/'AspisR1Stage2ResumeSuffix/FunsExternal.olean'),('funs',SRC/'AspisR1Stage2ResumeSuffix/Funs.lean',OBJ/'AspisR1Stage2ResumeSuffix/Funs.olean'),('proof',SRC/'ClaimReadDecoderMap.lean',OBJ/'ClaimReadDecoderMap.olean')]
records=[];sampled=0;start=time.monotonic();before=(cg/'memory.events').read_text()
for name,source,dest in steps:
    cmd=[str(lean),'-M4400','-j1','-R',str(SRC),'-o',str(dest),str(source)]
    log=OUT/(name+'.lean.log'); timing=OUT/(name+'.time.log'); t0=time.monotonic()
    with log.open('w') as f:
        p=subprocess.Popen(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=SRC,env=env,stdout=f,stderr=subprocess.STDOUT)
        while p.poll() is None:
            sampled=max(sampled,int((cg/'memory.current').read_text())); time.sleep(.2)
        p.wait()
    ts=timing.read_text(); m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',ts); s=re.search(r'Swaps: (\d+)',ts)
    records.append({'name':name,'cmd':cmd,'exit':p.returncode,'wall_s':time.monotonic()-t0,'maxrss_kib':int(m[1]) if m else None,'process_swaps':int(s[1]) if s else None,'source_sha256':sha(source),'object_sha256':sha(dest) if dest.exists() else None,'log':str(log),'time_log':str(timing)})
    if p.returncode: break
receipt={'phase':'proof','exit_status':records[-1]['exit'],'wall_seconds':time.monotonic()-start,'peak_sampled_cgroup_bytes':sampled,'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'scope_limits':limits,'source_revision':C['source_revision'],'runner_sha256':sha(Path(__file__)),'config_sha256':sha(W/'config.json'),'prefix_objects':str(prefix),'reader_success_objects':str(reader),'reader_types_objects':str(reader_types),'reader_success_sha256':sha(reader/'Stage2ReaderSuccess.olean'),'prefix_objects_sha256':sha(prefix/'Stage2GeneratedPrefixCallCanonicality.olean'),'lean_path':leanpath,'direct_imports':{n:sha(prefix/(n+'.olean')) if (prefix/(n+'.olean')).is_file() else None for n in ['Stage2GeneratedPrefixCallCanonicality','AspisR1RecordParser/Funs','AspisR1DecodeKFullV10/Funs']},'steps':records,'classification':'Focused decoder-success transport for the isolated claim/rhs/power cut; no whole resume reachability claim.'}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
raise SystemExit(receipt['exit_status'])
