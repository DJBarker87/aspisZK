"""Link once, replay ax2 fixtures/roots and the byte-identical NFX scan.
All children inherit the existing capped launcher scope. No Lean compilation.
"""
from pathlib import Path
import json,subprocess,time,re,os,hashlib,sys
B=Path(__file__).resolve().parent;T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
parent=json.loads((B/os.environ['NHN_REVIEW_CONFIG']).read_text());roots=json.loads((B/'NHN_AUDIT_ROOTS.json').read_text())['roots']
out=B/os.environ.get('NHN_REVIEW_OUTPUT','NHN_review');out.mkdir(exist_ok=False)
cmds=[('link',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NHN_native/NHN_Driver','NHN_native/NHN_Driver.c','NHN_native/NFA_WALKER.c','NHN_native/NFA_MemoryLimit.c'])]
cmds += [(mode,['NHN_native/NHN_Driver',mode]) for mode in ['fixtures']+[f'proof{i}'for i in range((len(roots)+9)//10)]+['scan']]
rows=[]
for name,cmd in cmds:
 start=time.monotonic();log=out/(name+'.log');tim=out/(name+'.time.log')
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 wall=time.monotonic()-start;s=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip()for l in stats.splitlines()if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=wall,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=parent['source_revision'],parent_attempt=parent['attempt'],print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=[json.loads(l[11:])for l in s.splitlines()if l.startswith('NEP_RESULT ')])
 (out/(name+'.json')).write_text(json.dumps(row,indent=1)+'\n');rows.append(row)
 print(json.dumps(dict(target=name,exit=r.returncode,wall_seconds=wall,peak_rss_kib=row['peak_rss_kib'],roots=len(row['results']))),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if name.startswith('proof'):
  assert row['results']and all(x['equal']and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in row['results'])
 elif name=='fixtures':
  assert len(row['results'])==8 and all(x['equal']for x in row['results'])
  assert all(len(x['walked_axioms'])==1 for x in row['results'][:4])and all(not x['walked_axioms']for x in row['results'][4:])
 elif name=='scan':
  scan=[json.loads(l)for l in (B/'NHN_LOADED_scan.jsonl').read_text().splitlines()]
  assert scan and all(x['imports_match']and not x['dangling']and not x.get('duplicate_owners')for x in scan)
  selected=[];search=parent['env']['LEAN_PATH'].split(':')
  for x in scan:
   rel=x['module'].replace('.','/')+'.olean';p=next((Path(r)/rel for r in search if (Path(r)/rel).is_file()),None);assert p is not None,rel
   for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
    if z.is_file():selected.append(dict(module=x['module'],path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size))
  (out/'SELECTED_CLOSURE.json').write_text(json.dumps(selected,indent=1)+'\n')
  (out/'SCAN_SUMMARY.json').write_text(json.dumps(dict(modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0,cached_replicas=sum(len(x.get('cached_replicas',[]))for x in scan)),indent=1)+'\n')
assert set(roots)=={x['root']for r in rows for x in r['results']if r['target'].startswith('proof')}
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows),indent=1)+'\n')
p=B/'NHN_native/NHN_Driver';(out/'BINARY_PIN.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size),indent=1)+'\n')
