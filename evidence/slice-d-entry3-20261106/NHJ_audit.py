"""One capped link/fixture/raw-audit/scan gate; unchanged hardened walker."""
from pathlib import Path
import subprocess,json,time,re,hashlib,sys
B=Path(__file__).resolve().parent;T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
parents=[json.loads(p.read_text()) for p in B.glob('NHJ_L???.json')];parent=next(x for x in parents if x['kind']=='audit')
for obj in parent['deps_fingerprint']['selected_objects'].values():assert hashlib.sha256(Path(obj['path']).read_bytes()).hexdigest()==obj['sha256']
out=B/'NHJ_audit';out.mkdir(exist_ok=False)
commands=[]
for name in ['NHJ_ProofDriver','NHJ_ScanDriver']:
 commands.append(('link_'+name,[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NHJ_native/'+name,'NHJ_native/'+name+'.c','NHJ_native/NFA_WALKER.c','NHJ_native/NFA_MemoryLimit.c']))
commands += [(mode,['NHJ_native/NHJ_ProofDriver',mode]) for mode in ['fixtures','proof0']]
commands += [('scan',['NHJ_native/NHJ_ScanDriver','scan'])]
rows=[]
for name,cmd in commands:
 start=time.monotonic();log=out/(name+'.log');tim=out/(name+'.time.log');binary=B/cmd[0] if not name.startswith('link_') else None
 before=hashlib.sha256(binary.read_bytes()).hexdigest() if binary else None
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 wall=time.monotonic()-start;s=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip() for l in stats.splitlines() if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=wall,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=parent['source_revision'],parent_attempt=parent['attempt'],print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')])
 if binary:assert hashlib.sha256(binary.read_bytes()).hexdigest()==before;row['same_optimized_binary_sha256']=before
 (out/(name+'.json')).write_text(json.dumps(row,indent=1)+'\n');rows.append(row);print(json.dumps(dict(target=name,exit=r.returncode,wall_seconds=wall,peak_rss_kib=row['peak_rss_kib'],roots=len(row['results']))),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if name=='fixtures':
  assert len(row['results'])==8 and all(x['equal'] for x in row['results'])
  assert all(len(x['walked_axioms'])==1 for x in row['results'][:4]) and all(not x['walked_axioms'] for x in row['results'][4:])
 elif name=='proof0':assert len(row['results'])==3 and all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in row['results'])
 elif name=='scan':
  scan=[json.loads(l) for l in (B/'NHJ_LOADED_scan.jsonl').read_text().splitlines()]
  assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in scan)
  (out/'scan_summary.json').write_text(json.dumps(dict(modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),indent=1))
assert next(r for r in rows if r['target']=='fixtures')['same_optimized_binary_sha256']==next(r for r in rows if r['target']=='proof0')['same_optimized_binary_sha256']
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows),indent=1)+'\n')
for name in ['NHJ_ProofDriver','NHJ_ScanDriver']:
 p=B/'NHJ_native'/name;(out/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
