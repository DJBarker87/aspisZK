from pathlib import Path
import fcntl, hashlib, json, subprocess, sys

work=Path(__file__).resolve().parent
stage=sys.argv[1]
evidence=work/stage
evidence.mkdir(exist_ok=False)
collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock_path=Path('/tmp/aspis-global-extraction-admission-20261019.lock')
with lock_path.open('a') as lock:
    try: fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:
        (evidence/'admission.json').write_text(json.dumps({'allowed':False,'not_started':True,'reason':'global admission lock busy'})+'\n')
        raise SystemExit(75)
    raw=subprocess.check_output(['python3',str(collector)],text=True)
    (evidence/'reservation-inventory.json').write_text(raw)
    inv=json.loads(raw)
    reserved=inv['effective_sum_bytes']
    finite=[Path(row['path']) for row in inv['effective_reservation_nodes']]
    unbounded=[]
    for row in inv['unbounded_populated_scopes']:
        p=Path(row['path'])
        if any(p==f or f in p.parents for f in finite): continue
        if any(Path(other['path']) in p.parents for other in inv['unbounded_populated_scopes']): continue
        unbounded.append(row)
    uncapped=sum(row['current_bytes'] or 0 for row in unbounded)
    requested=4*2**30; physical=inv['MemTotal_kB']*1024; avail=inv['MemAvailable_kB']*1024
    allowed=(reserved+requested <= 48*2**30 and reserved+requested+uncapped+8*2**30 <= physical and avail >= 14*2**30)
    adm={'allowed':allowed,'not_started':not allowed,'reserved_bytes':reserved,'requested_bytes':requested,
         'uncapped_populated_bytes':uncapped,'physical_bytes':physical,'available_bytes':avail,
         'os_reserve_bytes':8*2**30,'safe_reservation_ceiling_bytes':48*2**30,
         'minimum_available_bytes':14*2**30,'collector_sha256':sha(collector),
         'source_sha256':sha(work/'src/lib.rs')}
    (evidence/'admission.json').write_text(json.dumps(adm,indent=2)+'\n')
    print(json.dumps(adm),flush=True)
    if not allowed: raise SystemExit(78)
    cmd=['systemd-run','--user','--quiet','--wait','--collect','--service-type=exec',
         '-p','KillMode=control-group','-p','MemoryHigh=2G','-p','MemoryMax=4G','-p','MemorySwapMax=0',
         '-p',f'StandardOutput=append:{evidence}/scope.stdout.log',
         '-p',f'StandardError=append:{evidence}/scope.stderr.log',
         'python3',str(work/'in-scope.py'),str(evidence)]
    (evidence/'scope-command.json').write_text(json.dumps(cmd,indent=2)+'\n')
    proc=subprocess.run(cmd,cwd=work)
    raise SystemExit(proc.returncode)
