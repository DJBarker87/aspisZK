from pathlib import Path
import subprocess,json,time,hashlib,re,sys,os
B=Path.cwd();mode=sys.argv[1];E=B/'NMX_audit'/mode;E.mkdir(parents=True,exist_ok=True)
idx=int(mode.removeprefix('proof'));jobs=[(mode,['NMX_native/NMX_ProofDriver',mode])]
for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 expected=json.loads((B/'NMX_AUDIT_ROOTS.json').read_text())['groups'][idx]
 observed=receipt['results']
 valid=(len(observed)==len(expected) and {x['root'] for x in observed}==set(expected) and
  all(x['equal'] is True and set(x['walked_axioms']) <= {'propext','Classical.choice','Quot.sound'} for x in observed))
 receipt['standard_axioms_and_complete_roots']=valid
 if not valid:receipt['exit_status']=9
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt),flush=True)
 if receipt['exit_status']:print(raw,flush=True);sys.exit(receipt['exit_status'])
