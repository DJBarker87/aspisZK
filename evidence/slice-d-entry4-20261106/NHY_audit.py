"""Own adapted driver; unchanged hardened walker; optimized link and eight controls."""
from pathlib import Path
import subprocess,json,time,re,hashlib,sys
B=Path(__file__).resolve().parent;T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
parent=max((json.loads(p.read_text()) for p in B.glob('NHY_L???.json') if json.loads(p.read_text())['kind']=='audit'),key=lambda x:x['attempt'])
for obj in parent['deps_fingerprint']['selected_objects'].values():assert hashlib.sha256(Path(obj['path']).read_bytes()).hexdigest()==obj['sha256']
out=B/parent['module'];out.mkdir(exist_ok=False);mode='proof'+str(int(parent['module'].split('stage')[1].split('_')[0])-1)
commands=[]
for name in ['ProofDriver','ScanDriver']:
 if not (B/('NHY_native/NHY_'+name)).exists():commands.append(('link_'+name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NHY_native/NHY_'+name,'NHY_native/NHY_'+name+'.c','NHY_native/NFA_WALKER.c','NHY_native/NFA_MemoryLimit.c']))
commands += [(m,['NHY_native/NHY_ScanDriver' if m=='scan' else 'NHY_native/NHY_ProofDriver',m]) for m in json.loads((B/'NHY_AUDIT_PLAN.json').read_text())]
rows=[]
for name,cmd in commands:
 start=time.monotonic();log=out/(name+'.log');tim=out/(name+'.time.log');before=None if name.startswith('link_') else hashlib.sha256((B/cmd[0]).read_bytes()).hexdigest()
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip() for l in stats.splitlines() if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=parent['source_revision'],parent_attempt=parent['attempt'],same_optimized_binary_sha256=before,print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')])
 (out/(name+'.json')).write_text(json.dumps(row,indent=1)+'\n');rows.append(row)
 print(json.dumps(dict(target=name,exit=r.returncode,wall_seconds=row['wall_seconds'],peak_rss_kib=row['peak_rss_kib'],roots=len(row['results']))),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if before:assert hashlib.sha256((B/cmd[0]).read_bytes()).hexdigest()==before
 if name=='fixtures':
  assert len(row['results'])==8 and all(x['equal'] for x in row['results'])
  assert all(len(x['walked_axioms'])==1 for x in row['results'][:4]) and all(not x['walked_axioms'] for x in row['results'][4:])
 elif name==mode:
  assert len(row['results'])==len(json.loads((B/'NHY_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])])
  assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in row['results'])
 elif name=='scan':
  scan=[json.loads(l) for l in (B/'NHY_LOADED_scan.jsonl').read_text().splitlines()]
  assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in scan)
  (out/'scan_summary.json').write_text(json.dumps(dict(modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),indent=1))
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows,proof_group=mode),indent=1)+'\n')
