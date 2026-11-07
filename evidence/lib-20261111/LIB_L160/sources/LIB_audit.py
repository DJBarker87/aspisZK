"""Own audit client; unchanged pinned ledger25 raw ax2 binary, own roots only."""
from pathlib import Path
import json,hashlib,subprocess,sys,time,re
B=Path.cwd();mode=sys.argv[1];assert re.fullmatch(r'proof[0-9]+',mode)
roots=json.loads((B/'LIB_AUDIT_ROOTS.json').read_text());index=int(mode[5:]);expected=roots['groups'][index]
assert all(n.startswith('LIB_') for n in expected)
for name in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:
 (B/('NLX_'+name)).write_bytes((B/('LIB_'+name)).read_bytes())
pin=json.loads((B/'LIB_AUDITOR_PIN.json').read_text());binary=Path(pin['binary'])
assert hashlib.sha256(binary.read_bytes()).hexdigest()==pin['sha256'],'Auditor binary drift'
E=B/'LIB_audit'/mode;E.mkdir(parents=True,exist_ok=True);start=time.monotonic()
command=[str(binary),mode]
with (E/(mode+'.log')).open('w')as f:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(mode+'.time')),*command],stdout=f,stderr=subprocess.STDOUT)
raw=(E/(mode+'.log')).read_text();timing=(E/(mode+'.time')).read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')]
standard={'Classical.choice','Quot.sound','propext'}
valid=r.returncode==0 and sorted(z['root']for z in results)==sorted(expected) and all(z['equal'] is True and set(z['walked_axioms'])<=standard and set(z['collect_axioms'])==set(z['walked_axioms']) for z in results)
receipt=dict(target=mode,command=command,exit_status=r.returncode,validated=valid,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=results,auditor=pin,manifest_sha256=hashlib.sha256((B/'LIB_AUDIT_ROOTS.json').read_bytes()).hexdigest())
(E/(mode+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(target=mode,exit=r.returncode,validated=valid,roots=len(results),wall=receipt['wall_seconds'])))
if not valid:print(raw)
sys.exit(0 if valid else 1)
