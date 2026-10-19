#!/usr/bin/env python3
"""Build the isolated visitor fix; retain pinned compiler/cache unchanged."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time

base=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
task=Path('/home/dombarker/project-offloads/aspis-r1-cu-equivalence-20261019')
here=Path(__file__).resolve().parent
out=task/'aeneas-single-visit'
limits={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((here/'aeneas-single-visit-pins.json').read_text())
run=lambda a:subprocess.check_output(a,text=True).strip()
finite=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        if p.read_text().strip()!='max' and 'populated 1' in (p.parent/'cgroup.events').read_text():
            finite.append((str(p.parent),int(p.read_text())))
    except OSError:pass
reservations=[(p,n) for p,n in finite if not any(p.startswith(q+'/') for q,_ in finite if q!=p)]
assert sum(n for _,n in reservations)+8*2**30<=50*2**30,reservations
assert sha(base/'aeneas/src/interp/InterpBorrowsCore.ml')==pins['original_source_sha256']
out.mkdir(exist_ok=False)
# copy2 preserves reusable Dune objects but never shares writable source inodes.
shutil.copytree(base/'aeneas',out/'aeneas',symlinks=True)
subprocess.run(['patch','--batch','-p1','-i',str(here/'aeneas-single-visit.patch')],cwd=out/'aeneas',check=True)
assert sha(out/'aeneas/src/interp/InterpBorrowsCore.ml')==pins['patched_source_sha256']
shutil.copy2(here/'build-aeneas-single-visit.sh',out/'build.sh')
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
name='aspis-cu-aeneas-single-visit-20261019'
command=['docker','create','--name',name,'--network','none','--read-only',
    '--memory','8g','--memory-swap','8g','--pids-limit','128','--cap-drop','ALL',
    '--security-opt','no-new-privileges','--tmpfs','/tmp:rw,nosuid,size=256m',
    '--mount',f'type=bind,src={out}/aeneas,dst=/work/aeneas',
    '--mount',f'type=bind,src={base}/charon,dst=/work/charon,readonly',
    '--mount',f'type=bind,src={out},dst=/out',
    '--entrypoint','/bin/bash',image,'/out/build.sh']
cid=run(command)
run(['docker','start',name])
state=json.loads(run(['docker','inspect',name]))[0]
assert state['Image']==image
pid=state['State']['Pid']
relative=Path(f'/proc/{pid}/cgroup').read_text().split('0::',1)[1].strip()
cg=Path('/sys/fs/cgroup')/relative.lstrip('/')
assert cid in str(cg)
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','docker-'+cid+'.scope',
    'MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0'],check=True)
assert {k:(cg/k).read_text().strip() for k in limits}==limits
preflight=dict(command=command,compiler_command=['dune','build','--profile','release','-j1','main.exe'],
    source_revision=os.environ['ASPIS_SOURCE_REVISION'],features=[],pins=pins,
    build_script_sha256=sha(out/'build.sh'),runner_sha256=sha(Path(__file__)),
    container_id=cid,image=image,cgroup=str(cg),limits=limits,reservations_before=reservations,
    expected_work='Incremental optimized OCaml compiler rebuild from copied Dune objects; no Charon/sysroot/Lean rebuild.',
    print_axioms='N/A: frontend build; Lean consuming targets require separate axioms audits')
(out/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
before=Path('/proc/meminfo').read_text()
(out/'compile-go').write_text('Actual compiler cgroup cap verified.\n')
start=time.monotonic();peak=0;stopped=False;last={}
while True:
    state=json.loads(run(['docker','inspect',name]))[0]
    if not state['State']['Running']:break
    if cg.exists():
        last={k:(cg/k).read_text().strip() for k in ['memory.current','memory.peak','memory.swap.current','memory.events']}
        peak=max(peak,int(last['memory.current']))
    if time.monotonic()-start>600:
        run(['docker','stop','-t','5',name]);stopped=True;break
    time.sleep(.5)
state=json.loads(run(['docker','inspect',name]))[0];status=state['State']['ExitCode']
timing=(out/'compile-time.log').read_text() if (out/'compile-time.log').is_file() else ''
def metric(label):
    m=re.search(re.escape(label)+r':\s*(\d+)',timing)
    return int(m[1]) if m else None
receipt=dict(preflight,exit_status=status,wall_seconds=time.monotonic()-start,
    peak_rss_kib=metric('Maximum resident set size (kbytes)'),process_swaps=metric('Swaps'),
    sampled_cgroup_peak_bytes=peak,last_cgroup_observation=last,mandatory_review_stop=stopped,
    host_swap_before=[s for s in before.splitlines() if s.startswith('Swap')],
    host_swap_after=[s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('Swap')],
    binary_sha256=sha(out/'bin/aeneas') if status==0 else None)
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_kib','process_swaps','binary_sha256']}))
raise SystemExit(status)
