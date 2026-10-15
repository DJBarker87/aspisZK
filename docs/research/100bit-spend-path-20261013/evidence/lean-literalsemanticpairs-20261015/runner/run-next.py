#!/usr/bin/env python3
"""Focused local checks using an existing, hash-recorded cache. No dependency builds."""
import hashlib, json, os, re, signal, subprocess, sys, time
from pathlib import Path
ROOT=Path('/tmp/aspis-root-local-semantic-20261015')
REPO=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
SOURCES=REPO/'docs/research/100bit-spend-path-20261013/lean'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    target,label=sys.argv[1:]
    assert re.fullmatch(r'Literal[A-Za-z]+',target)
    assert re.fullmatch(r'[a-z0-9-]+',label)
    attempts=ROOT/'attempts'
    assert not any(p for p in attempts.glob(label+'.*') if not p.name.endswith('.time.log')), 'refuse existing attempt'
    src=ROOT/'sources'/('R1'+target+'.lean')
    src.write_bytes((SOURCES/(target+'.lean')).read_bytes())
    snapshot=attempts/(label+'.source.lean'); snapshot.write_bytes(src.read_bytes())
    out=ROOT/'objects'/('R1'+target+'.olean')
    assert not out.exists(), 'refuse overwrite object'
    direct=[]
    for module in re.findall(r'^import (\S+)',src.read_text(),re.M):
        obj=ROOT/'objects'/(module.replace('.','/')+'.olean')
        assert obj.exists(), 'missing direct import '+module
        direct.append({'module':module,'object_path':str(obj),'object_sha256':sha(obj)})
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
    pre={'source_sha256':sha(src),'source_base_revision':revision,'direct_imports':direct,'runner_sha256':sha(Path(__file__))}
    (attempts/(label+'.preflight.json')).write_text(json.dumps(pre,indent=2)+'\n')
    cmd=['/Users/dominic/.elan/bin/lake','env','python3',str(ROOT/'lean-with-cache.py'),str(ROOT/'objects'),'-M5000','-R',str(ROOT/'sources'),'-o',str(out),str(src)]
    peak=0; start=time.monotonic(); killed=False
    with (attempts/(label+'.log')).open('x') as log:
        p=subprocess.Popen(cmd,cwd='/Users/dominic/ZK/AspisFormal',stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
            rss=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid)
            peak=max(peak,rss)
            if rss>7*1024*1024 or time.monotonic()-start>900:
                killed=True; os.killpg(p.pid,signal.SIGKILL); break
            time.sleep(.1)
        status=p.wait()
    rec={**pre,'target':target,'attempt':label,'command':cmd,'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_process_group_rss_kib_sampled':peak,'stop_threshold_kib':7*1024*1024,'lean_memory_limit_mb':5000,'timeout_seconds':900,'killed_for_memory_or_timeout':killed,'no_cgroup_used':True,'note':'Local focused cache reuse; process swap count in external time log; not a cold transitive replay.'}
    if out.exists(): rec['object_sha256']=sha(out)
    (attempts/(label+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec))
    return status
if __name__=='__main__': raise SystemExit(main())
