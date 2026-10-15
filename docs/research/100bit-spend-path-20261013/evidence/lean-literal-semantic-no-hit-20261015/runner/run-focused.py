#!/usr/bin/env python3
import hashlib,json,os,signal,subprocess,sys,time
from pathlib import Path
ROOT=Path('/tmp/aspis-root-local-semantic-20261015')
FALLBACK=Path('/Users/dominic/ZK/.worktrees/r1-j1-r7-r8-20261015/.j1-local-check/objects')
MERGE=Path('/Users/dominic/ZK/.worktrees/r1-j1-r11-r12-20261015/.j1-merge-check/objects')
LAKE=Path('/Users/dominic/.elan/bin/lake')
LIMIT_KIB=7*1024*1024
MAP={'LiteralC1Prefix':'LiteralC1Prefix.lean','LiteralSemanticViewComponents':'LiteralSemanticViewComponents.lean'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    if len(sys.argv)!=3 or sys.argv[1] not in MAP: raise SystemExit('usage: run-focused.py TARGET ATTEMPT_LABEL')
    target,label=sys.argv[1],sys.argv[2]; src=ROOT/'sources'/('R1'+MAP[target])
    meta=json.loads((ROOT/'preflight.json').read_text())
    if sha(src)!=meta['source_pins'][MAP[target]]['sha256']: raise SystemExit('source snapshot hash changed')
    for name,rec in meta['object_overlay'].items():
        obj=ROOT/'objects'/name
        if not obj.exists() or sha(obj)!=rec['sha256']: raise SystemExit('object overlay pin mismatch: '+name)
    out=ROOT/'objects'/('R1'+target+'.olean')
    if out.exists(): raise SystemExit('refusing to overwrite output object: '+str(out))
    attempts=ROOT/'attempts'
    if (attempts/(label+'.json')).exists() or (attempts/(label+'.log')).exists(): raise SystemExit('refusing to overwrite attempt')
    env=dict(os.environ); paths=[str(ROOT/'objects')]
    if FALLBACK.is_dir(): paths.append(str(FALLBACK))
    if MERGE.is_dir(): paths.append(str(MERGE))
    env['LEAN_PATH']=':'.join(paths+[env.get('LEAN_PATH','')])
    cmd=[str(LAKE),'env','python3',str(ROOT/'lean-with-cache.py'),':'.join(paths),'-M5000','-R',str(ROOT/'sources'),'-o',str(out),str(src)]
    start=time.monotonic(); peak=0; killed=False
    with (attempts/(label+'.log')).open('x') as log:
        p=subprocess.Popen(cmd,cwd='/Users/dominic/ZK/AspisFormal',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
            rss=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid)
            peak=max(peak,rss)
            if rss>LIMIT_KIB or time.monotonic()-start>900:
                killed=True; os.killpg(p.pid,signal.SIGKILL); break
            time.sleep(.1)
        status=p.wait()
    record={'target':target,'attempt':label,'source_sha256':sha(src),'command':cmd,'cwd':'/Users/dominic/ZK/AspisFormal','exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_process_group_rss_kib_sampled':peak,'stop_threshold_kib':LIMIT_KIB,'killed_for_memory_or_timeout':killed,'timeout_seconds':900,'lean_memory_limit_mb':5000,'incoming_j1_local_check_fallback':str(FALLBACK),'incoming_j1_local_check_present_at_run':FALLBACK.is_dir(),'observed_merge_check_fallback':str(MERGE),'observed_merge_check_present_at_run':MERGE.is_dir(),'object_overlay_manifest':str(ROOT/'preflight.json'),'source_base_revision':meta['source_base_revision'],'no_cgroup_used':True}
    with (attempts/(label+'.json')).open('x') as f: json.dump(record,f,indent=2); f.write('\n')
    return status
if __name__=='__main__': raise SystemExit(main())
