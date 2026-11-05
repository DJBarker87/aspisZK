"""Unchanged ax2 semantics: optimized driver link, eight same-binary controls,
all named new roots with headline, then unchanged NFX owner/import scan."""
from pathlib import Path
import subprocess,json,time,re,hashlib,os,sys,shutil
B=Path(__file__).resolve().parent;parent=json.loads((B/sys.argv[1]).read_text());T=parent['env']['LEAN_SYSROOT']
out=B/(parent['attempt']+'_audit');out.mkdir(exist_ok=False)
commands=[]
for name in ['NGV_ProofDriver','NGV_Driver']:
 commands.append(('link_'+name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGV_native/'+name,'NGV_native/'+name+'.c','NGV_native/NFA_WALKER.c','NGV_native/NFA_MemoryLimit.c']))
groups=json.loads((B/'NGV_AUDIT_ROOTS.json').read_text())['groups']
commands += [(mode,['NGV_native/NGV_ProofDriver',mode]) for mode in ['fixtures']+[f'proof{i}'for i in range(len(groups))]]
commands += [('scan',['NGV_native/NGV_Driver','scan'])]
rows=[]
for name,cmd in commands:
 start=time.monotonic();log=out/(name+'.log');tim=out/(name+'.time.log')
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 wall=time.monotonic()-start;s=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip()for l in stats.splitlines()if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=wall,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=parent['source_revision'],parent_attempt=parent['attempt'],print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=[json.loads(l[11:])for l in s.splitlines()if l.startswith('NEP_RESULT ')])
 (out/(name+'.json')).write_text(json.dumps(row,indent=1));rows.append(row)
 print(json.dumps(dict(target=name,exit=r.returncode,wall_seconds=wall,peak_rss_kib=row['peak_rss_kib'],roots=len(row['results']))),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if name.startswith('proof') or name=='fixtures':
  assert row['results'] and all(x['equal']for x in row['results'])
  if name=='fixtures':
   assert len(row['results'])==8 and all(len(x['walked_axioms'])==1 for x in row['results'][:4])and all(not x['walked_axioms']for x in row['results'][4:])
  else:assert all(set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in row['results'])
 if name=='scan':
  shutil.copyfile(B/'NGV_LOADED_scan.jsonl',out/'LOADED_scan.jsonl')
  scan=[json.loads(l) for l in (B/'NGV_LOADED_scan.jsonl').read_text().splitlines()]
  assert len(scan)>12000 and all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in scan)
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows),indent=1))
for name in ['NGV_ProofDriver','NGV_Driver']:
 p=B/'NGV_native'/name;(out/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
