"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys,os
B=Path.cwd();mode=sys.argv[1];E=B/'NLX_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='close':
 exec(compile((B/'NLX_pin.py').read_text(),'NLX_pin.py','exec'));sys.exit(0)
if mode=='retention':jobs=[('retention',['python3','NLX_scope40.py'])]
elif mode=='review-close':jobs=[('review',[os.environ['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NLX_generated','-o','NLX_objects/NLX_HypothesisReview.olean','NLX_generated/NLX_HypothesisReview.lean'])]
elif mode.startswith('inventory-'):jobs=[(mode,['NLX_native/NLX_InventoryDriver',mode.split('-')[1]])]
elif mode in ['poolfixtures','poolroots','poolscan']:jobs=[('scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0',['NLX_native/'+('NLX_PoolDriver' if mode=='poolscan' else 'NLX_PoolProofDriver'), 'scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0'])]
elif mode in ['fixtures','scan','scan2']:jobs=[('scan' if mode=='scan2' else mode,['NLX_native/'+('NLX_Driver' if mode.startswith('scan') else 'NLX_ProofDriver'),'scan' if mode=='scan2' else mode])]
else:
 parts=mode.removeprefix('batch').split('-');batch=int(parts[0]);last=int(parts[-1]);groups=json.loads((B/'NLX_AUDIT_ROOTS.json').read_text())['groups'];jobs=[('proof'+str(i),['NLX_native/NLX_ProofDriver','proof'+str(i)]) for i in range(batch,min(last+1,len(groups)))];assert jobs
for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt),flush=True)
 if r.returncode:print(raw,flush=True);sys.exit(r.returncode)

if mode=='review-close':
 print(raw,flush=True)
 exec(compile((B/'NLX_pin.py').read_text(),'NLX_pin.py','exec'))
