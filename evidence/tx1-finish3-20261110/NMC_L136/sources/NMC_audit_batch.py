"""One independently receipted audit target per admitted scope; raw verdict retained."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys,os,lzma
B=Path.cwd();mode=sys.argv[1];E=B/'NMC_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='close':
 exec(compile((B/'NMC_pin.py').read_text(),'NMC_pin.py','exec'));exec(compile((B/'NMC_preflight.py').read_text(),'NMC_preflight.py','exec'));sys.exit(0)
command=['NMC_native/'+('NMC_Driver'if mode=='scan'else'NMC_ProofDriver'),mode]
start=time.monotonic()
with (E/(mode+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(mode+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
raw=(E/(mode+'.log')).read_text();timing=(E/(mode+'.time')).read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1]if m else None
results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')]
receipt=dict(target=mode,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines()if 'depends on axioms'in l or 'does not depend on any axioms'in l],results=results)
(E/(mode+'.json')).write_text(json.dumps(receipt,indent=1)+'\n')
for p in B.glob('NEP_'+mode+'_*'):
 if p.is_file():
  blob=p.read_bytes();(E/(p.name+'.xz')).write_bytes(lzma.compress(blob));(E/(p.name+'.sha256')).write_text(hashlib.sha256(blob).hexdigest()+'\n')
print(json.dumps(dict(target=mode,exit=r.returncode,results=len(results),peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'])),flush=True)
sys.exit(r.returncode)
