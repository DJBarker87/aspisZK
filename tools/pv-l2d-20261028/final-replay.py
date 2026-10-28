"""ONE requested frozen focused replay in the single private coherent view.
On transport loss recover the submitted receipt read-only; never resubmit.
No prior full manifest of this helper closure was run. CtZero is a standalone
primitive audit at reserved ID51597, followed by the two combined audits.
"""
from pathlib import Path
import json,subprocess,hashlib,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
x=json.loads((E/'final-focused-manifest.json').read_text());assert len(x['replay'])==32
progress=[]
for row in x['replay']+x['audits']:
 m=row['module'];a=row['attempt'];s=R/row['source_path'];assert hashlib.sha256(s.read_bytes()).hexdigest()==row['source_sha256']
 p=E/f'receipt-{a}.json'
 if not p.exists():
  q=subprocess.run([sys.executable,str(R/'tools/pv-l2d-20261028/private-lean.py'),str(a),m],text=True,capture_output=True)
  (E/f'final-launcher-{a}.log').write_text(q.stdout+q.stderr)
  if q.returncode:
   print('STOP',a,m,'exit',q.returncode, q.stdout[-800:]+q.stderr[-800:],flush=True);sys.exit(q.returncode)
 v=json.loads(p.read_text());assert v['target']==m and v['source_sha256']==row['source_sha256'] and v['exit']==0,v
 assert all('sorryAx' not in z for z in v['axioms'])
 progress.append(dict(attempt=a,module=m,exit=v['exit'],wall=v['wall'],peak_rss_kib=v['peak_rss_kib'],swaps=v['swaps']))
 (E/'final-replay-progress.json').write_text(json.dumps(progress,indent=2)+'\n')
 print(a,m,'PASS',v['wall'],v['peak_rss_kib'],'KiB swap',v['swaps'],flush=True)
print('FINAL FOCUSED REPLAY AND AUDITS COMPLETE',len(progress),flush=True)
