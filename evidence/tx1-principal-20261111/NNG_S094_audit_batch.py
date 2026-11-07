"""One distinct raw ax2 group, fixtures, or NFX scan per capped scope."""
from pathlib import Path
import json,subprocess,sys,hashlib,time,re,lzma
B=Path.cwd();mode=sys.argv[1];E=B/'NNG_S094_audit'/mode;E.mkdir(parents=True,exist_ok=True)
for n,h in json.loads((B/'NNG_S094_AUDIT_MANIFEST_PINS.json').read_text()).items():assert hashlib.sha256((B/n).read_bytes()).hexdigest()==h,n
for name in ['NNG_S094_ProofDriver']:
 pin=json.loads((B/(name+'_BINARY_PIN.json')).read_text());assert hashlib.sha256(Path(pin['path']).read_bytes()).hexdigest()==pin['sha256'],name
command=['NNG_native/'+('NNG_S094_Driver'if mode=='scan'else'NNG_S094_ProofDriver'),mode]
start=time.monotonic()
with(E/(mode+'.log')).open('w')as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(mode+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
raw=(E/(mode+'.log')).read_text();tim=(E/(mode+'.time')).read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',tim);return m[1]if m else None
results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')]
receipt=dict(target=mode,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines()if'depends on axioms'in l or'does not depend on any axioms'in l],results=results)
(E/(mode+'.json')).write_text(json.dumps(receipt,indent=1))
if mode=='fixtures':
 selected=['NEP_Planted.matcher','NEP_Planted.viaPrivate','NEP_Planted.proof','NEP_Planted.viaAux','NEP_MutateMatch.matcher','NEP_MutatePrivate.viaPrivate','NEP_MutateProof.proof','NEP_MutateAux.viaAux']
else:selected=json.loads((B/'NNG_S094_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])]
for p in B.glob('NEP_'+mode+'_*'):
 if not any(p.name.startswith('NEP_'+mode+'_'+root+'_') for root in selected):continue
 if p.is_file():
  data=p.read_bytes();(E/(p.name+'.xz')).write_bytes(lzma.compress(data,preset=6));(E/(p.name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'\n')
print(json.dumps(dict(target=mode,exit=r.returncode,results=len(results),peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'])),flush=True);sys.exit(r.returncode)
