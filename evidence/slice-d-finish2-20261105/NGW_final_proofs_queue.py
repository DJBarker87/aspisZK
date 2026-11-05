from pathlib import Path
import subprocess,time,json
E=Path(__file__).resolve().parent
while not (E/'NGW_K100/receipt.json').exists():
 if 'isolate' in (E/'NGW_FINISH_NATIVE_QUEUE.log').read_text():break
 time.sleep(2)
for a,n in [('NGW_L065','NGW_NewInterface'),('NGW_L071','NGW_DotRef/Types'),('NGW_L072','NGW_DotRef/Funs'),('NGW_L073','NGW_DotCodec'),('NGW_L074','NGW_CurrentAddPort')]:
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean',n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
