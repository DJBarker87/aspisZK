#!/usr/bin/env python3
"""Run one focused existing env-J executor, retaining unedited raw receipts."""
import datetime, hashlib, json, pathlib, re, shlex, subprocess, sys, time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
HOST = 'dombarker@100.108.41.90'
JOB = '/home/dombarker/project-offloads/codex-pv-l2b-20261027'
T = '/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
LAUNCH = '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh'
RESERVE = '/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
attempt, source = int(sys.argv[1]), pathlib.Path(sys.argv[2]).resolve()
if (HERE/'attempts.jsonl').exists() and len((HERE/'attempts.jsonl').read_text().splitlines())>=100:
    print('Lean attempt budget exhausted');sys.exit(64)
assert 53000 <= attempt <= 53299
assert source.is_relative_to(ROOT) and source.name.startswith('PV_L2B_')
for old in list((HERE/'receipts').glob('*/reservation.json'))+list((HERE/'kani').glob('*/reservation.json'))+list(HERE.glob('batch-*/reservation.json')):
    try:
        gate=json.loads(old.read_text())
        if gate.get('allowed') is not False:continue
        stamp=gate.get('utc')
        when=float(stamp) if isinstance(stamp,(float,int)) else datetime.datetime.fromisoformat(stamp).timestamp()
        wait=(30 if 'error' in gate else 180)-(time.time()-when)
        if wait>0:
            (HERE/'receipts'/f'{attempt}-local-hold.json').write_text(json.dumps({'attempt':attempt,'charged':False,'reason':'mandatory local reservation timer','remaining_seconds':wait})+'\n')
            print(f'Mandatory reservation wait: {wait:.1f}s remaining from {old}');sys.exit(78)
    except (ValueError,TypeError):pass
dest = HERE / 'receipts' / str(attempt)
assert not dest.exists(), 'never reuse attempt IDs'
dest.mkdir(parents=True)
(dest/'source.lean').write_bytes(source.read_bytes())
def ssh(cmd):
    return subprocess.run(['ssh', HOST, cmd], text=True, capture_output=True)
rev = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
pre = ssh(f'python3 {RESERVE} {JOB}/reservation-{attempt}.json > {JOB}/reservation-{attempt}.log 2>&1; cat {JOB}/reservation-{attempt}.log')
(dest/'preflight.log').write_text(pre.stdout+pre.stderr)
reservation = ssh(f'cat {JOB}/reservation-{attempt}.json')
if not reservation.stdout.strip():
    (dest/'refused.json').write_text(json.dumps({'attempt':attempt,'charged':False,'reason':'missing reservation JSON; scanner failure; retry after 30 seconds'}))
    print(pre.stdout+pre.stderr);sys.exit(78)
(dest/'reservation.json').write_text(reservation.stdout)
if not json.loads(reservation.stdout)['allowed']:
    (dest/'refused.json').write_text(json.dumps({'attempt':attempt,'charged':False,'revision':rev}))
    print('RESERVATION HOLD: '+reservation.stdout[:400],flush=True)
    sys.exit(78)
subprocess.run(['scp','-q',str(source),f'{HOST}:{JOB}/{source.name}'],check=True)
imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
dep_code='''import json,pathlib,hashlib,sys
env=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
paths=[sys.argv[1]]+env['LEAN_PATH'].split(':')
out=[]
for m in json.loads(sys.argv[2]):
 p=next((pathlib.Path(r)/(m.replace('.','/')+'.olean') for r in paths if (pathlib.Path(r)/(m.replace('.','/')+'.olean')).is_file()),None)
 out.append({'module':m,'path':str(p) if p else None,'sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p else None})
print(json.dumps(out,sort_keys=True))'''
deps=ssh(shlex.join(['python3','-c',dep_code,JOB,json.dumps(imports)]))
(dest/'dependencies.json').write_text(deps.stdout)
fingerprint=hashlib.sha256(deps.stdout.encode()).hexdigest()
# Existing env-J executor, task-owned roots. The fixed shared launcher rejects
# external sources under -R (53000); do not change it or shared source files.
module = source.stem
start=time.monotonic()
p=ssh(' '.join(map(shlex.quote,[
 'systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G',
 '-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',f'{JOB}/time-{attempt}.log',
 'timeout','900','python3',f'{T}/run2.py',
 '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json',
 JOB,JOB,f'{JOB}/{source.stem}.olean',f'{JOB}/{source.name}','7000'
 ]))+f' > {JOB}/out-{attempt}.log 2>&1; result=$?; echo exit=$result >> {JOB}/out-{attempt}.log; cat {JOB}/out-{attempt}.log')
(dest/'launcher.log').write_text(p.stdout+p.stderr)
for name, remote in [('out.log',f'{JOB}/out-{attempt}.log'),('time.log',f'{JOB}/time-{attempt}.log')]:
    r=ssh('cat '+shlex.quote(remote)); (dest/name).write_text(r.stdout+r.stderr)
out=(dest/'out.log').read_text(); timing=(dest/'time.log').read_text()
exit_match=re.search(r'^exit=(\d+)',out,re.M)
receipt={'attempt':attempt,'module':source.stem,'target':module,'revision':rev,
 'source':str(source.relative_to(ROOT)),'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'launcher_exit':p.returncode,'exit':int(exit_match[1]) if exit_match else None,
 'wall_client_seconds':time.monotonic()-start,'deps_fingerprint':fingerprint,
 'axioms':re.findall(r"'[^\n]+(?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out),
 'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'lean_M':7000,'TasksMax':64}}
for key, pattern in [('wall',r'Elapsed \(wall clock\) time.*: (.+)'),('peak_RSS_KiB',r'Maximum resident set size \(kbytes\): (\d+)'),('swap',r'Swaps: (\d+)')]:
    m=re.search(pattern,timing);receipt[key]=m[1] if m else None
(dest/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
with (HERE/'attempts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps({k:receipt[k] for k in ['attempt','module','exit','wall','peak_RSS_KiB','swap']}),flush=True)
if receipt['exit'] != 0:print(out[-10000:],flush=True)
sys.exit(0 if receipt['exit']==0 else 1)
