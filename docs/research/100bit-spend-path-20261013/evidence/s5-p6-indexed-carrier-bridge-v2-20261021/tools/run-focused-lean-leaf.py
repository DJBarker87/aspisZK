#!/usr/bin/env python3
"""Reusable capped local Lean leaf runner; invoke with one JSON config path.

Config keys: repo_root, target, source, output, evidence_dir, lean, lean_path,
imports (name -> {path, sha256}), lock (optional), lean_memory_mib (default 4400),
wait_seconds (default 55), timeout_seconds (default 120), aggregate_rss_abort_bytes
(default 7.5 GiB). Captures Git HEAD only after winning the lock and confirming
no other Lean executable is live. Uses the existing warm objects only.
"""
from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time

cfgp=Path(sys.argv[1]).resolve()
cfg=json.loads(cfgp.read_text())
repo=Path(cfg['repo_root']).resolve(); source=Path(cfg['source']).resolve(); out=Path(cfg['output']).resolve()
ev=Path(cfg['evidence_dir']).resolve(); ev.mkdir(parents=True,exist_ok=True); out.parent.mkdir(parents=True,exist_ok=True)
lock=Path(cfg.get('lock','/tmp/aspis-local-lean.lock.d'))
lean=Path(cfg['lean']).resolve(); roots=[Path(x).resolve() for x in cfg['lean_path']]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
wait_seconds=int(cfg.get('wait_seconds',55)); deadline=time.monotonic()+wait_seconds

def live_lean_pids():
    rows=subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines(); result=[]
    for row in rows:
        a=row.strip().split(None,1)
        if len(a)==2 and Path(a[1]).name=='lean': result.append(int(a[0]))
    return result

while True:
    if live_lean_pids():
        if time.monotonic()>=deadline:
            (ev/'denied.json').write_text(json.dumps({'status':'LIVE_LEAN_TIMEOUT','wait_seconds':wait_seconds})+'\n')
            raise SystemExit(75)
        time.sleep(1); continue
    try: lock.mkdir()
    except FileExistsError:
        if time.monotonic()>=deadline:
            (ev/'denied.json').write_text(json.dumps({'status':'LOCK_BUSY_TIMEOUT','wait_seconds':wait_seconds})+'\n')
            raise SystemExit(75)
        time.sleep(1); continue
    (lock/'owner.json').write_text(json.dumps({'pid':os.getpid(),'target':cfg['target']}))
    active=live_lean_pids()
    if active:
        try:(lock/'owner.json').unlink()
        except FileNotFoundError:pass
        try:lock.rmdir()
        except OSError:pass
        if time.monotonic()>=deadline:
            (ev/'denied.json').write_text(json.dumps({'status':'LIVE_LEAN_RACE_TIMEOUT','pids':active,'wait_seconds':wait_seconds})+'\n')
            raise SystemExit(75)
        time.sleep(1); continue
    break
try:
    source_sha=sha(source); lean_sha=sha(lean)
    selected={}
    for name,pin in cfg.get('imports',{}).items():
        path=Path(pin['path']).resolve(); actual=sha(path)
        if actual!=pin['sha256']: raise SystemExit(f'IMPORT_PIN_MISMATCH {name}: {actual}')
        selected[name]={'path':str(path),'sha256':actual}
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
    now=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
    limit={'threads':1,'lean_memory_mib':int(cfg.get('lean_memory_mib',4400)),
      'aggregate_rss_abort_bytes':int(cfg.get('aggregate_rss_abort_bytes',int(7.5*1024**3))),
      'timeout_seconds':int(cfg.get('timeout_seconds',120))}
    pre={'target':cfg['target'],'source':str(source),'source_sha256':source_sha,'source_revision':revision,
      'launch_time_utc':now,'lean':str(lean),'lean_sha256':lean_sha,'direct_imports':selected,
      'warm_roots':[str(x) for x in roots],'limits':limit,'no_dependency_builds':True,
      'admission':{'lock':str(lock),'live_lean_pids':active,'status':'lock acquired; no other Lean process live'}}
    (ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
    env=os.environ.copy(); env['LEAN_PATH']=':'.join(str(x) for x in roots)
    argv=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+env['LEAN_PATH'],str(lean),
       '-j1','-M',str(limit['lean_memory_mib']),'-R',str(source.parent),'-o',str(out),str(source)]
    (ev/'command.json').write_text(json.dumps({'argv':argv,'cwd':str(repo),'source_revision':revision,
      'source_sha256':source_sha,'launcher':str(Path(__file__).resolve()),'launcher_sha256':sha(__file__),
      'config':str(cfgp),'config_sha256':sha(cfgp),'launch_time_utc':now,'lock':str(lock)},indent=2)+'\n')
    def rss_tree(pid):
        rows={}
        for row in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines():
            a,b,c=map(int,row.split()); rows[a]=(b,c*1024)
        selected={pid}; changed=True
        while changed:
            add={p for p,(pp,_) in rows.items() if pp in selected}-selected
            changed=bool(add); selected|=add
        return sum(rows.get(p,(0,0))[1] for p in selected)
    started=time.monotonic(); peak=0; abort=None
    with (ev/'lean.log').open('w') as log:
        proc=subprocess.Popen(argv,cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            peak=max(peak,rss_tree(proc.pid))
            if peak>=limit['aggregate_rss_abort_bytes'] or time.monotonic()-started>limit['timeout_seconds']:
                abort='aggregate RSS cap' if peak>=limit['aggregate_rss_abort_bytes'] else 'timeout'
                os.killpg(proc.pid,signal.SIGTERM)
                try: proc.wait(timeout=3)
                except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL)
                break
            time.sleep(.1)
        code=proc.wait()
    txt=(ev/'time.log').read_text()
    def extract(pattern):
        m=re.search(pattern,txt); return int(m.group(1)) if m else None
    receipt={'target':cfg['target'],'exit_status':code,'wall_seconds':round(time.monotonic()-started,3),
      'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':extract(r'(\d+)\s+maximum resident set size'),
      'swap_bytes':extract(r'(\d+)\s+swaps'),'watchdog_abort':abort,'source_revision':revision,
      'source_sha256':source_sha,'object_sha256':sha(out) if out.is_file() else None}
    (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True); raise SystemExit(code)
finally:
    try:(lock/'owner.json').unlink()
    except FileNotFoundError:pass
    try:lock.rmdir()
    except OSError:pass
