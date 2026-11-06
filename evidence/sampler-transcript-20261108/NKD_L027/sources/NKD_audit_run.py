"""One dynamic audit invocation, retaining exact verdicts, metrics and raw ax2 output."""
from pathlib import Path
import subprocess,json,sys,re,time,lzma,hashlib
B=Path.cwd();mode=sys.argv[1];d=B/'NKD_audit'/mode;d.mkdir(parents=True,exist_ok=True)
command=['NKD_native/'+('NKD_Driver'if mode=='scan'else 'NKD_ProofDriver'),mode]
start=time.monotonic()
with(d/'stdout.log').open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(d/'time.log'),*command],stdout=f,stderr=subprocess.STDOUT)
raw=(d/'stdout.log').read_text();timing=(d/'time.log').read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1]if m else None
receipt=dict(target=mode,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines()if 'depends on axioms'in l or 'does not depend on any axioms'in l],results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')])
(d/'receipt.json').write_text(json.dumps(receipt,indent=1)+'\n')
for p in list(B.glob('NEP_*'))+[B/'NKD_LOADED_scan.jsonl']:
 if p.is_file()and p.suffix not in ['.xz','.sha256']:
  data=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(data));Path(str(p)+'.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
print(json.dumps(dict(target=mode,exit_status=r.returncode,results=len(receipt['results']))))
sys.exit(r.returncode)
