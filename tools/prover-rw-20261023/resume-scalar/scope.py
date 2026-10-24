"""Verify own scope and aggregate before executing one extraction."""
from pathlib import Path
import json,runpy,subprocess,sys,hashlib,time
O=Path(sys.argv[1]);cmd=sys.argv[2:]
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},limits
scan=runpy.run_path(str(Path(__file__).resolve().parent/'reservation.py'))
r=scan['admission'](requested=0);r.update(own_cgroup=str(cg),limits=limits,command=cmd)
(O/'admission-barrier.json').write_text(json.dumps(r,indent=2)+'\n');assert r['allowed']
pre=json.loads((O/'preflight.json').read_text())
go={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in pre['source_sha256']}
(O/'go-hashes.json').write_text(json.dumps(dict(utc=time.time(),source_sha256=go),indent=2)+'\n')
assert go==pre['source_sha256'],'input changed before go'
(O/'target-started.json').write_text(json.dumps(dict(command=cmd,utc=time.time()))+'\n')
proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd])
peak_rss=0;peak_swap=0;samples=0
while True:
    rss=0
    for group in [cg,*cg.rglob('*')]:
        if not group.is_dir():continue
        procs=group/'cgroup.procs'
        if not procs.exists():continue
        for pid in procs.read_text().split():
            try:
                status=Path('/proc')/pid/'status'
                fields=dict(line.split(':',1) for line in status.read_text().splitlines() if ':' in line)
                rss+=int(fields.get('VmRSS','0 kB').split()[0])
            except FileNotFoundError:pass
    peak_rss=max(peak_rss,rss);peak_swap=max(peak_swap,int((cg/'memory.swap.current').read_text()));samples+=1
    result=proc.poll()
    if result is not None:break
    time.sleep(0.25)
(O/'resources.json').write_text(json.dumps(dict(sampled_peak_aggregate_rss_kib=peak_rss,sampling_interval_seconds=0.25,samples=samples,cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),peak_swap_bytes=peak_swap,limits=limits),indent=2)+'\n')
raise SystemExit(result)
