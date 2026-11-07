"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys
B=Path.cwd();mode=sys.argv[1];E=B/'NMS_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='R2_scan':jobs=[('scan',['NMS_native/NMS_R2Driver','scan'])]
elif mode.startswith('R2_batch'):
 batch=int(mode.removeprefix('R2_batch'));groups=json.loads((B/'NMS_R2_AUDIT_ROOTS.json').read_text())['groups']
 jobs=[('proof'+str(batch),['NMS_native/NMS_R2Driver','proof'+str(batch)])];assert batch<len(groups)
else:raise ValueError(mode)

for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt),flush=True)
 if r.returncode:print(json.dumps({'audit_failure_log':str(E/(name+'.log'))}),flush=True);sys.exit(r.returncode)
