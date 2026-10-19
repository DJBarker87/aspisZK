#!/usr/bin/env python3
"""Run the two projected-oracle differential tests in isolated 8 GiB scopes."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
ATTEMPT = Path(__file__).resolve().parent
KIT = ATTEMPT / 'input'
TARGET = ATTEMPT / 'target-projected-tests-20261017'
CARGO = Path('/home/dombarker/.cargo/bin/cargo')
LIMITS = {'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':'0','TasksMax':'128'}
TESTS = [
    'factorized_projected_oracle_matches_reference_at_extreme_field_values',
    'optimized_oracle_matches_independent_reference_at_random_off_domain_points',
]
ENV = {**os.environ,
    'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',
    'RUSTUP_TOOLCHAIN':'nightly-2026-06-01', 'CARGO_BUILD_JOBS':'1',
    'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3',
    'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true',
    'RUSTFLAGS':'-C overflow-checks=yes', 'CARGO_TARGET_DIR':str(TARGET),
    'CARGO_NET_OFFLINE':'true'}

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()

def reservation_snapshot(stage):
    units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
    active=0; scopes=[]
    for line in units.splitlines():
        fields=line.split()
        if not fields: continue
        unit=fields[0]
        out=subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','ControlGroup'],text=True)
        d=dict(x.split('=',1) for x in out.splitlines() if '=' in x)
        scopes.append({'unit':unit,**d})
        if unit=='init.scope': continue
        raw=d.get('MemoryMax','infinity')
        if raw=='infinity': raise SystemExit('unbounded active scope: '+unit)
        active+=int(raw)
    external=24*1024**3; ours=8*1024**3
    current_path=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/memory.current')
    current=int(current_path.read_text().strip()) if current_path.exists() else None
    processes=subprocess.check_output(['ps','-eo','args'],text=True).splitlines()
    writers=[x for x in processes if str(TARGET) in x and re.search(r'(^|/)(cargo|rustc)( |$)',x)]
    rec={'stage':stage,'utc':subprocess.check_output(['date','-u','+%FT%TZ'],text=True).strip(),'active_scopes':scopes,'active_finite_max_bytes':active,'external_reservation_bytes':external,'this_scope_reservation_bytes':ours,'projected_total_bytes':active+external+ours,'policy_limit_bytes':50*1024**3,'memory_current_bytes':current,'shared_target_writers':writers,'check':'pass' if active+external+ours<=50*1024**3 and not writers else 'fail'}
    d=ATTEMPT/'reservations'; d.mkdir(exist_ok=True); (d/(stage+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
    if rec['check']!='pass': raise SystemExit('reservation check failed')

def run_inside():
    name=sys.argv[2]; cmd=json.loads(sys.argv[3]); out=ATTEMPT/'test-logs'; out.mkdir(exist_ok=True)
    log=out/(name+'.log'); receipt=out/(name+'.json'); start=time.monotonic(); wall=time.time()
    with log.open('x') as f:
        proc=subprocess.run(['/usr/bin/time','-v','timeout','--signal=KILL','300',*cmd],cwd=KIT,env=ENV,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text(errors='replace'); rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',text)
    cg=''
    for line in Path('/proc/self/cgroup').read_text().splitlines():
        if line.startswith('0::'): cg=line[3:]; break
    cgr=Path('/sys/fs/cgroup')/cg.lstrip('/')
    def read(k):
        try:return (cgr/k).read_text().strip()
        except:return None
    rec={'test':name,'command':cmd,'exit_status':proc.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(rss.group(1)) if rss else None,'cgroup':cg,'memory_peak_bytes':read('memory.peak'),'swap_peak_bytes':read('memory.swap.peak'),'swap_current_bytes':read('memory.swap.current'),'memory_events':read('memory.events'),'memory_high':read('memory.high'),'memory_max':read('memory.max'),'memory_swap_max':read('memory.swap.max'),'scope_limits':LIMITS,'started_unix':wall,'source_sha256':sha(KIT/'src/statement/state_only_poseidon.rs'),'manifest_sha256':sha(ATTEMPT/'candidate-source-manifest.json'),'runner_sha256':sha(Path(__file__))}
    receipt.write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec),flush=True); sys.exit(proc.returncode)

if len(sys.argv)>1 and sys.argv[1]=='inside': run_inside()
for test in TESTS:
    reservation_snapshot(test)
    cmd=[str(CARGO),'test','--manifest-path',str(KIT/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--features','r0,pool-v1-kernel','--no-default-features','--release','--locked','--offline','--lib',test]
    unit='aspis-explicit-low-folds-'+test+'-20261017'
    scope=['systemd-run','--user','--scope','--quiet','--unit='+unit]
    for k,v in LIMITS.items(): scope+=['--property='+k+'='+v]
    scope += [sys.executable,str(Path(__file__).resolve()),'inside',test,json.dumps(cmd,separators=(',',':'))]
    result=subprocess.run(scope,cwd=ATTEMPT,env=ENV,text=True,capture_output=True,timeout=360)
    launches=ATTEMPT/'scope-launches'; launches.mkdir(exist_ok=True)
    (launches/(test+'.json')).write_text(json.dumps({'test':test,'argv':scope,'exit_status':result.returncode,'stdout':result.stdout,'stderr':result.stderr,'limits':LIMITS},indent=2)+'\n')
    print(json.dumps({'test':test,'exit_status':result.returncode,'stdout':result.stdout,'stderr':result.stderr}),flush=True)
    if result.returncode: sys.exit(result.returncode)
