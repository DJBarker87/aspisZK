from pathlib import Path
import subprocess,lzma,json,sys
E=Path(__file__).resolve().parent
jobs=[('PCD_K039',None),('PCD_K040','assertion failed'),('PCD_K041',None),('PCD_K042','assertion failed'),('PCD_K025',None),('PCD_K026','assertion failed'),('PCD_K027',None),('PCD_K028','assertion failed')]
for a,negative in jobs:
 r=subprocess.run([sys.executable,str(E/'PCD_native_run.py'),a],capture_output=True,text=True)
 log=E/a/'stdout.log.xz'
 if not log.exists():print(a+' no scope receipt: '+(r.stdout+r.stderr)[-400:],flush=True);sys.exit(1)
 s=lzma.decompress(log.read_bytes()).decode()
 expected=('VERIFICATION:- SUCCESSFUL' in s) if negative is None else ('VERIFICATION:- FAILED' in s and 'Failed Checks:' in s and 'timed out' not in s and 'unwinding assertion' not in s)
 marker=s[s.rfind('Failed Checks:'):s.find('\n',s.rfind('Failed Checks:'))] if negative else 'SUCCESSFUL'
 print(a+' expected-verdict='+str(expected)+' '+marker[:180],flush=True)
 if not expected:sys.exit(1)
