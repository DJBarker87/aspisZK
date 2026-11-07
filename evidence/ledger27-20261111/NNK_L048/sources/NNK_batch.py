"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys,os
B=Path.cwd();mode=sys.argv[1];
# The unchanged binary has legacy manifest names baked in; these are private input aliases only.
for n in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:
 (B/('NLX_'+n)).write_bytes((B/('NNK_'+n)).read_bytes())
E=B/'NNK_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='close':
 exec(compile((B/'NNK_pin.py').read_text(),'NNK_pin.py','exec'));exec(compile((B/'NNK_scope40.py').read_text(),'NNK_scope40.py','exec'));sys.exit(0)
if mode=='acc-close':jobs=[('combined',[os.environ['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNK_generated','-o','NNK_objects/NNK_COMBINED_IMPORT.olean','NNK_generated/NNK_COMBINED_IMPORT.lean']),('scan',['NNK_native/NNK_Driver','scan'])]
elif mode in ['verify','verify-retention']:jobs=[('verify',['python3','NNK_gate_check.py'])]
elif mode=='retention':jobs=[('retention',['python3','NNK_scope40.py'])]
elif mode in ['review-close','review-retention']:jobs=[('review',[os.environ['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNK_generated','-o','NNK_objects/NNK_HypothesisReview.olean','NNK_generated/NNK_HypothesisReview.lean'])]
elif mode in ['split41a','split41b']:jobs=[('proof'+str(i),['NNK_native/NNK_ProofDriver','proof'+str(i)])for i in [41 if mode=='split41a'else 48]]
elif mode.startswith('inventory-'):jobs=[(mode,['NNK_native/NNK_InventoryDriver',mode.split('-')[1]])]
elif mode in ['poolfixtures','poolroots','poolscan']:jobs=[('scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0',['NNK_native/'+('NNK_PoolDriver' if mode=='poolscan' else 'NNK_PoolProofDriver'), 'scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0'])]
elif mode in ['fixtures','scan','scan2']:jobs=[('scan' if mode=='scan2' else mode,['NNK_native/'+('NNK_Driver' if mode.startswith('scan') else 'NNK_ProofDriver'),'scan' if mode=='scan2' else mode])]
else:
 parts=mode.removeprefix('batch').split('-');batch=int(parts[0]);last=int(parts[-1]);groups=json.loads((B/'NNK_AUDIT_ROOTS.json').read_text())['groups'];jobs=[('proof'+str(i),['NNK_native/NNK_ProofDriver','proof'+str(i)]) for i in range(batch,min(last+1,len(groups)))];assert jobs
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
 exec(compile((B/'NNK_pin.py').read_text(),'NNK_pin.py','exec'))

if mode=="review-retention":
 exec(compile((B/"NNK_scope40.py").read_text(),"NNK_scope40.py","exec"))

if mode=='acc-close':
 exec(compile((B/'NNK_pin.py').read_text(),'NNK_pin.py','exec'))
 exec(compile((B/'NNK_scope40.py').read_text(),'NNK_scope40.py','exec'))

if mode=='verify-retention':
 exec(compile((B/'NNK_scope40.py').read_text(),'NNK_scope40.py','exec'))
