"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys,os
B=Path.cwd();mode=sys.argv[1];
# The unchanged binary has legacy manifest names baked in; these are private input aliases only.
for n in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:
 (B/('NLX_'+n)).write_bytes((B/('NNI_'+n)).read_bytes())
E=B/'NNI_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='close':
 exec(compile((B/'NNI_pin.py').read_text(),'NNI_pin.py','exec'));exec(compile((B/'NNI_scope40.py').read_text(),'NNI_scope40.py','exec'));sys.exit(0)
if mode=='retention':jobs=[('retention',['python3','NNI_scope40.py'])]
elif mode in ['review-close','review-retention']:jobs=[('review',[os.environ['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNI_generated','-o','NNI_objects/NNI_HypothesisReview.olean','NNI_generated/NNI_HypothesisReview.lean'])]
elif mode.startswith('inventory-'):jobs=[(mode,['NNI_native/NNI_InventoryDriver',mode.split('-')[1]])]
elif mode in ['poolfixtures','poolroots','poolscan']:jobs=[('scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0',['NNI_native/'+('NNI_PoolDriver' if mode=='poolscan' else 'NNI_PoolProofDriver'), 'scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0'])]
elif mode in ['fixtures','scan','scan2']:jobs=[('scan' if mode=='scan2' else mode,['NNI_native/'+('NNI_Driver' if mode.startswith('scan') else 'NNI_ProofDriver'),'scan' if mode=='scan2' else mode])]
else:
 parts=mode.removeprefix('batch').split('-');batch=int(parts[0]);last=int(parts[-1]);groups=json.loads((B/'NNI_AUDIT_ROOTS.json').read_text())['groups'];jobs=[('proof'+str(i),['NNI_native/NNI_ProofDriver','proof'+str(i)]) for i in range(batch,min(last+1,len(groups)))];assert jobs
for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt),flush=True)
 if r.returncode:print(raw,flush=True);sys.exit(r.returncode)

if mode in ['review-close','review-retention']:
 print(raw,flush=True)
 exec(compile((B/'NNI_pin.py').read_text(),'NNI_pin.py','exec'))

if mode=="review-retention":
 exec(compile((B/"NNI_scope40.py").read_text(),"NNI_scope40.py","exec"))
