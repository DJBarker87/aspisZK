from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,m in [('NBG_L066','NBG_Reducer'),('NBG_L067','NBG_GetterPorts'),('NBG_L068','NBG_WideBytes'),('NBG_L069','NBG_Error'),('NBG_L070','NBG_PaymentChecks')]:
 assert len(list(E.glob('NBG_L*/receipt.json')))<98
 r=subprocess.run([sys.executable,str(E/'NBG_build.py'),a,'lean/'+m+'.lean',m],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,'driver',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 print('result',json.loads((E/a/'receipt.json').read_text())['exit_status'],flush=True)
