"""One capped final audit gate: optimized link, fixtures, selected raw roots.

No Lean compilation occurs here. Each child command has its own full timing
receipt, and every child inherits the already verified scope limits.
"""
from pathlib import Path
import subprocess,json,time,re,hashlib,os,sys
B=Path(__file__).resolve().parent
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
parent=json.loads((B/'NFU_L005.json').read_text())
out=B/'NFU_final_audit';out.mkdir(exist_ok=False)
commands=[('link',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NFU_native/NFU_ProofDriver','NFU_native/NFU_ProofDriver.c','NFU_native/NFA_WALKER.c','NFU_native/NFA_MemoryLimit.c'])]
commands += [(mode,['NFU_native/NFU_ProofDriver',mode]) for mode in ['fixtures']+[f'proof{i}' for i in range(1)]]
rows=[]
for name,cmd in commands:
 start=time.monotonic();log=out/(name+'.log');tim=out/(name+'.time.log')
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 wall=time.monotonic()-start;s=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip() for l in stats.splitlines() if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=wall,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=parent['source_revision'],parent_attempt='NFU_L005',print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')])
 (out/(name+'.json')).write_text(json.dumps(row,indent=1)+'\n');rows.append(row)
 print(json.dumps(dict(target=name,exit=r.returncode,wall_seconds=wall,peak_rss_kib=row['peak_rss_kib'],roots=len(row['results']))),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if name!='link':
  assert row['results'] and all(x['equal'] for x in row['results'])
  if name=='fixtures':
   assert len(row['results'])==8
   assert all(len(x['walked_axioms'])==1 for x in row['results'][:4])
   assert all(not x['walked_axioms'] for x in row['results'][4:])
  else:
   assert all(set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in row['results'])
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows),indent=1)+'\n')
p=B/'NFU_native/NFU_ProofDriver';(out/'BINARY_PIN.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size),indent=1)+'\n')
