from pathlib import Path
import subprocess,json,time,re,hashlib,sys
B=Path.cwd();T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';out=B/'NGM_final_audit';out.mkdir(exist_ok=False)
commands=[]
for target in ['NGM_ProofDriver','NGM_Driver']:
 commands.append(('link_'+target,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGM_native/'+target,'NGM_native/'+target+'.c','NGM_native/NFA_WALKER.c','NGM_native/NFA_MemoryLimit.c']))
commands += [('fixtures',['NGM_native/NGM_ProofDriver','fixtures']),('proof0',['NGM_native/NGM_ProofDriver','proof0']),('scan',['NGM_native/NGM_Driver','scan'])]
rows=[]
for name,cmd in commands:
 log=out/(name+'.log');tim=out/(name+'.time.log');start=time.monotonic()
 with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 raw=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip() for l in stats.splitlines() if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",raw),results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 (out/(name+'.json')).write_text(json.dumps(row,indent=1)+'\n');rows.append(row);print(json.dumps({k:row[k]for k in ['target','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 if name in ['fixtures','proof0']:
  assert row['results'] and all(z['equal']for z in row['results'])
  if name=='fixtures':
   assert len(row['results'])==8 and all(len(z['walked_axioms'])==1 for z in row['results'][:4]) and all(not z['walked_axioms']for z in row['results'][4:])
  else:assert all(set(z['walked_axioms'])==set(z['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}for z in row['results'])
 if name=='scan':
  scan=[json.loads(l)for l in (B/'NGM_LOADED_scan.jsonl').read_text().splitlines()]
  assert scan and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
  (out/'SCAN_SUMMARY.json').write_text(json.dumps(dict(status='PASS',modules=len(scan),dangling=sum(len(r['dangling'])for r in scan),incompatible_owners=sum(len(r['duplicate_owners'])for r in scan),import_mismatches=sum(not r['imports_match']for r in scan)),indent=2)+'\n')
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows),indent=1)+'\n')
(B/'NGM_final_audit/SCAN.jsonl').write_bytes((B/'NGM_LOADED_scan.jsonl').read_bytes())
