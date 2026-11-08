"""One 180-second audit window; unchanged optimized NNM walker and fixtures."""
from pathlib import Path
import json,hashlib,subprocess,time,re,sys,shutil
B=Path.cwd();mode=sys.argv[1];E=B/'NNO_audit'/mode;E.mkdir(parents=True,exist_ok=True)
P=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111')
walker=P/'NNM_native/NNM_ProofDriver';assert hashlib.sha256(walker.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
for n in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:(B/('NLX_'+n)).write_bytes((B/('NNO_'+n)).read_bytes())
failed=False
for name,cmd in [('fixtures',[str(walker),'fixtures']),('proof0',[str(walker),'proof0']),('scan',['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','--run','NNO_RuntimeScan.lean','scan'])]:
 start=time.monotonic()
 with(E/(name+'.log')).open('w')as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),'timeout','180',*cmd],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1]if m else None
 x=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines()if'depends on axioms'in l or'does not depend on any axioms'in l],results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x),flush=True)
 if r.returncode:failed=True
sys.exit(1 if failed else 0)
