"""Own validator; unchanged raw ax2 binary and NFX canonical-owner algorithm."""
from pathlib import Path
import subprocess,json,hashlib,sys,time,re,os
B=Path.cwd();mode=sys.argv[1];assert mode=='fixtures' or mode in ['scan','fullimport','buildscan'] or re.fullmatch(r'proof[0-9]+',mode)
for n in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:(B/('NLX_'+n)).write_bytes((B/('PCM_'+n)).read_bytes())
pin=json.loads((B/'PCM_AUDITOR_PIN.json').read_text());binary=Path(pin['binary']);assert hashlib.sha256(binary.read_bytes()).hexdigest()==pin['sha256']
E=B/'PCM_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='buildscan':
 (B/'PCM_native').mkdir(exist_ok=True)
 commands=[[os.environ['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-c','PCM_native/PCM_Scan.c','-o','PCM_objects/PCM_Scan.olean','PCM_Scan.lean'],[os.environ['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','PCM_native/PCM_Scan','PCM_native/PCM_Scan.c']]
 for c in commands:
  r=subprocess.run(c)
  if r.returncode:sys.exit(r.returncode)
 (B/'PCM_NATIVE_SCANNER_PIN.json').write_text(json.dumps(dict(binary=str(B/'PCM_native/PCM_Scan'),sha256=hashlib.sha256((B/'PCM_native/PCM_Scan').read_bytes()).hexdigest(),commands=commands)))
 print('PCM optimized canonical scanner built');sys.exit(0)
if mode=='fullimport':command=[os.environ['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','PCM_COMBINED_IMPORT.lean']
elif mode=='scan':
 p=json.loads((B/'PCM_NATIVE_SCANNER_PIN.json').read_text());assert hashlib.sha256(Path(p['binary']).read_bytes()).hexdigest()==p['sha256']
 command=[p['binary'],'scan']
else:command=[str(binary),mode]
start=time.monotonic()
with (E/'stdout.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/'time.log'),*command],stdout=f,stderr=subprocess.STDOUT)
raw=(E/'stdout.log').read_text();timing=(E/'time.log').read_text()
def metric(k):
 m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')]
standard={'Classical.choice','Quot.sound','propext'}
validation=False
if mode.startswith('proof'):
 expected=json.loads((B/'PCM_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])]
 validation=r.returncode==0 and sorted(z['root']for z in results)==sorted(expected) and all(z['equal']is True and set(z['walked_axioms'])<=standard and set(z['collect_axioms'])==set(z['walked_axioms'])for z in results)
elif mode=='fixtures':validation=r.returncode==0 and len(results)==8
elif mode=='fullimport':validation=r.returncode==0
else:
 p=B/'PCM_LOADED_scan.jsonl';rows=[json.loads(l)for l in p.read_text().splitlines()]if p.exists()else[]
 validation=r.returncode==0 and bool(rows) and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in rows)
 if p.exists():(E/'loaded_scan.jsonl').write_bytes(p.read_bytes())
receipt=dict(target=mode,scope='SUPPORTING_CLOSURE_ONLY_NOT_REQUIRED_GATE',command=command,exit_status=r.returncode,validated=validation,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),results=results,auditor=pin,source_revision='Recorded in enclosing scope receipt',standard_axioms=sorted(standard),manifest_sha256=hashlib.sha256((B/'PCM_AUDIT_ROOTS.json').read_bytes()).hexdigest())
(E/'validation.json').write_text(json.dumps(receipt,indent=1)+'\n')
print(json.dumps(dict(mode=mode,exit=r.returncode,validated=validation,roots=len(results))))
if not validation:print(raw[-1800:])
sys.exit(0 if validation else 1)
