#!/usr/bin/env python3
"""Freeze, stage, run and collect one changed focused source on the NUC."""
from pathlib import Path
import argparse, hashlib, json, resource, shlex, subprocess, sys, time

ap=argparse.ArgumentParser(); ap.add_argument('module'); ap.add_argument('attempt')
ap.add_argument('--axiom',action='append',default=[]);a=ap.parse_args()
repo=Path(__file__).resolve().parents[5]
area=repo/'docs/research/100bit-spend-path-20261013'
source=area/'lean'/(a.module+'.lean')
remote='/home/dombarker/project-offloads/aspis-r1-cu-equivalence-20261019'
host='dombarker@100.108.41.90'
out=area/'evidence/cu-equivalence-20261019'/a.attempt
out.mkdir(parents=True,exist_ok=False)
plan=dict(workspace=remote,lake_workspace='/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal',
    module=a.module,attempt=a.attempt,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),features=['pool-adapter','private-leaf-salts'],audit_declarations=a.axiom)
(out/'source.lean').write_bytes(source.read_bytes())
(out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
started=time.monotonic()
ssh_options=['-o','BatchMode=yes','-o','ConnectTimeout=10','-o','ConnectionAttempts=1',
    '-o','ServerAliveInterval=10','-o','ServerAliveCountMax=3']
def run(args,**kw): return subprocess.run(args,check=True,**kw)
staging=[['ssh',*ssh_options,host,'mkdir -p '+shlex.quote(remote+'/sources/'+str(Path(a.module).parent))],
    ['scp',*ssh_options,str(source),host+':'+remote+'/sources/'+a.module+'.lean'],
    ['scp',*ssh_options,str(Path(__file__).with_name('run-focused.py')),host+':'+remote+'/run-focused.py'],
    ['scp',*ssh_options,str(out/'plan.json'),host+':'+remote+'/'+a.attempt+'-plan.json']]
try:
    for command in staging:run(command)
except subprocess.CalledProcessError as error:
    usage=resource.getrusage(resource.RUSAGE_SELF)
    (out/'launcher-failure.json').write_text(json.dumps(dict(plan,phase='staging',
        failed_command=error.cmd,exit_status=error.returncode,
        launcher_wall_seconds=time.monotonic()-started,
        launcher_peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,
        launcher_process_swaps=usage.ru_nswap,proof_job_status='NOT_LAUNCHED',
        print_axioms='N/A: staging failed before launching Lean'),indent=2)+'\n')
    raise
command=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=128',
    'python3',remote+'/run-focused.py',remote+'/'+a.attempt+'-plan.json']
result=subprocess.run(['ssh',*ssh_options,host,shlex.join(command)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(out/'launcher.log').write_text(result.stdout)
try:
    run(['scp',*ssh_options,'-r',host+':'+remote+'/runs/'+a.attempt+'/.',str(out)])
except subprocess.CalledProcessError as error:
    (out/'launcher-failure.json').write_text(json.dumps(dict(plan,phase='receipt_collection',
        failed_command=error.cmd,exit_status=error.returncode,
        launcher_wall_seconds=time.monotonic()-started,proof_job_status='UNKNOWN',
        action='Inspect this same remote attempt before retrying; missing observation is not a terminal proof result'),indent=2)+'\n')
    raise
receipt=json.loads((out/'receipt.json').read_text())
print(receipt['print_axioms_output'])
print(json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_kib','process_swaps','source_sha256']}))
raise SystemExit(result.returncode)
