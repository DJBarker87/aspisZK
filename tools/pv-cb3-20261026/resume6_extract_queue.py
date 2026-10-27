"""Sequential native extraction queue; no unchanged failed extraction retries."""
from pathlib import Path
import subprocess,sys,json,datetime,time
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026'
state=out/'RESUME6_ADMISSION_STATE.json'
def status(d):
    if not d.get('attempt_charged',False):return 78
    return int(d['exit'])
args=sys.argv[1:];epoch='resume6q'
if args and args[0].startswith('--epoch='):
    epoch=args.pop(0).split('=',1)[1];assert epoch.isalnum()
for variant in args:
    for stage in ('charon','aeneas'):
        complete=[]
        for p in sorted(out.glob(f'{stage}-source-{variant}-{epoch}*/collected-receipt.json')):
            d=json.loads(p.read_text())
            if status(d)!=78:complete.append((p,d))
        if complete:
            p,d=complete[-1]
            print('reuse',p.name,p.parent.name,'exit',d['exit'],flush=True)
            if status(d)!=0:break
            continue
        for retry in range(10):
            if state.exists():
                d=json.loads(state.read_text())
                if not d.get('allowed',False):
                    left=datetime.datetime.fromisoformat(d['utc']).timestamp()+181-time.time()
                    if left>0:
                        print(f'cooldown {left:.1f}s before {stage} {variant}',flush=True)
                        time.sleep(left)
            n=1
            while (out/f'{stage}-source-{variant}-{epoch}{n}').exists():n+=1
            suffix=f'{epoch}{n}'
            code=subprocess.run([sys.executable,'-u',str(root/'tools/pv-cb3-20261026/resume6_extract.py'),stage,variant,suffix],cwd=root).returncode
            p=out/f'{stage}-source-{variant}-{suffix}/collected-receipt.json'
            if p.exists():
                result=status(json.loads(p.read_text()))
                if result!=78:break
            elif code!=78:sys.exit(code or 1)
        else:sys.exit(78)
        if result!=0:
            if stage=='charon':sys.exit(result)
            break
