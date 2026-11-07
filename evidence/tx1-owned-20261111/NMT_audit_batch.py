"""One bounded child; metric/complete result artifacts retained, concise stdout."""
from pathlib import Path
import json,subprocess,time,re,sys,os
B=Path.cwd();mode=sys.argv[1];E=B/'NMT_audit'/mode;E.mkdir(parents=True,exist_ok=True)
assert mode in ['fixtures','scan']or(re.fullmatch(r'proof[0-9]+',mode))
command=['NMT_native/'+('NMT_ScanDriver'if mode=='scan'else'NMT_ProofDriver'),mode]
start=time.monotonic()
with(E/(mode+'.log')).open('w')as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(mode+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
raw=(E/(mode+'.log')).read_text();timing=(E/(mode+'.time')).read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1]if m else None
receipt=dict(target=mode,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines()if'depends on axioms'in l or'does not depend on any axioms'in l],results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')])
(E/(mode+'.json')).write_text(json.dumps(receipt,indent=1)+'\n')
print(json.dumps(dict(mode=mode,exit=r.returncode,roots=len(receipt['results']),wall_seconds=receipt['wall_seconds'])),flush=True)
sys.exit(r.returncode)
