#!/usr/bin/env python3
"""Invoke retained analysis tools in private capped scopes and collect receipts."""
from pathlib import Path
import hashlib,json,shlex,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
H='/home/dombarker/project-offloads/codex-cx-lowering2-20261026';remote='dombarker@100.108.41.90'
name=sys.argv[1]; script='Low2_'+name+'.py'
label=name+('-'+sys.argv[2] if len(sys.argv)>2 else '')
cap='/home/dombarker/project-offloads/codex-cx-pin-20261020/harness/capped.py'
reserve='/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021/harness/reservation.py'
subprocess.run(['ssh',remote,shlex.join(['python3',reserve,H+'/'+label+'-reservation.json'])],check=True,stdout=(E/('Low2_'+label+'.reservation.log')).open('w'))
cmd=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',cap,H+'/'+label+'-receipt','Source hashing and retained S10 compiler ordering analysis; no arithmetic gate','--','timeout','180','python3',H+'/'+script]
r=subprocess.run(['ssh',remote,shlex.join(cmd)],capture_output=True,text=True)
(E/('Low2_'+label+'.launch.log')).write_text(r.stdout+r.stderr)
for f in ['receipt.json','time.log','stdout.log','stderr.log']:
 subprocess.run(['scp','-q',remote+':'+H+'/'+label+'-receipt/'+f,str(E/('Low2_'+label+'_'+f))],check=True)
subprocess.run(['scp','-q',remote+':'+H+'/'+label+'-reservation.json',str(E/('Low2_'+label+'_reservation.json'))],check=True)
(E/('Low2_'+label+'_invocation.json')).write_text(json.dumps({'command':cmd,'exit_status':r.returncode,'script_sha256':hashlib.sha256((E/script).read_bytes()).hexdigest(),'source_revision':json.loads((E/'Low2_build_inputs.json').read_text())['source_revision'],'print_axioms':'N/A: no Lean theorem'},indent=2)+'\n')
print(name,r.returncode,r.stdout,r.stderr);sys.exit(r.returncode)
