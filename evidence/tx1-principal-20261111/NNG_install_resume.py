from pathlib import Path
import json,subprocess,sys,time
E=Path(__file__).resolve().parent
while not (E/'NNG_L032/receipt.json').exists():time.sleep(1)
assert json.loads((E/'NNG_L032/receipt.json').read_text())['exit_status']==0
while (E/'NNG_CLIENT_ACTIVE').exists():time.sleep(1)
modules=['NNG_InstallBase','NNG_InstallRecord','NNG_InstallState','NNG_InstallPayload','NNG_InstallRounds','NNG_InputDomain','NNG_StdMapErr','NNG_StdEquality','NNG_StdArray','NNG_FinishTree']
for i,m in enumerate(modules,22):
 a=f'NNG_L{i:03}'
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run([sys.executable,str(E/'NNG_compile.py'),a,m])
 if r.returncode:raise SystemExit(r.returncode)
