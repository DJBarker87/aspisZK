"""Sequential own-directory extraction scopes, each admitted independently."""
from pathlib import Path
import subprocess,json,sys,time,datetime,hashlib
manifest=Path(sys.argv[1]);spec=json.loads(manifest.read_text());base=manifest.parent
scanner=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py')
left=spec['not_before']-time.time()
if left>0:print('cooldown',left,flush=True);time.sleep(left)
for plan in spec['plans']:
    name=plan['name'];dest=base/name;dest.mkdir(exist_ok=True)
    quiet=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
    until=float(json.loads(quiet.read_text()).get('until',0)) if quiet.exists() else 0
    if time.time()<until:
        (dest/'admission-before.json').write_text(json.dumps(dict(allowed=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reason='QUIET WINDOW HOLD',until=until)))
        sys.exit(78)
    p=subprocess.run(['python3',str(scanner),str(dest/'admission-before.json')],capture_output=True,text=True)
    (dest/'reservation.log').write_text(p.stdout+p.stderr)
    if p.returncode:print(name,'refused',flush=True);sys.exit(78)
    command=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',
        'python3',str(scanner.parent/'barrier.py'),str(dest/'admission-barrier.json'),
        '/usr/bin/time','-v','-o',str(dest/'time.log'),*plan['target']]
    for directory in plan.get('mkdir',[]):Path(directory).mkdir(exist_ok=True)
    with (dest/'output.log').open('w') as log:
        p=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
    (dest/'scope-exit.json').write_text(json.dumps(dict(exit=p.returncode)))
    print(name,'scope exit',p.returncode,flush=True)
    if not (dest/'time.log').exists():sys.exit(78)
    if p.returncode and plan['stage']=='charon':sys.exit(p.returncode)
    if p.returncode and plan['stage']=='aeneas':
        # A different root is a different obligation; skip only this root's remainder.
        continue
    if plan['stage']=='aeneas':
        trans=Path(plan['generated'])/'translation.json'
        if trans.exists():
            d=json.loads(trans.read_text());coverage=dict(functions=d.get('functions',[]),source='translation.json')
            (dest/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
            for filename in ('Funs.lean','Types.lean','translation.json'):
                src=Path(plan['generated'])/filename
                if src.exists():(dest/(filename+'.txt')).write_bytes(src.read_bytes())
