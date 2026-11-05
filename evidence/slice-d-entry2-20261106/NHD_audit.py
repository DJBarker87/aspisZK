"""Delta raw roots and a fresh NFX scan; reuse unchanged same-binary fixtures."""
from pathlib import Path
import subprocess,json,time,re,hashlib,sys
B=Path(__file__).resolve().parent
parents=[json.loads(p.read_text()) for p in B.glob('NHD_L???.json')]
parent=max((x for x in parents if x['kind']=='audit'),key=lambda x:x['attempt'])
for obj in parent['deps_fingerprint']['selected_objects'].values():assert hashlib.sha256(Path(obj['path']).read_bytes()).hexdigest()==obj['sha256']
reuse=json.loads((B/'NHD_REUSED_AUDIT.json').read_text())
for name in ['NHD_ProofDriver','NHD_ScanDriver']:
 pin=reuse['NHD_audit/'+name+'_BINARY_PIN.json'];p=B/'NHD_native'/name
 assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256'] and p.stat().st_size==pin['bytes']
fixture=reuse['NHD_audit/fixtures.json'];assert len(fixture['results'])==8 and fixture['exit_status']==0
assert all(x['equal'] for x in fixture['results']) and all(len(x['walked_axioms'])==1 for x in fixture['results'][:4]) and all(not x['walked_axioms'] for x in fixture['results'][4:])
assert fixture['same_optimized_binary_sha256']==reuse['NHD_audit/NHD_ProofDriver_BINARY_PIN.json']['sha256']
out=B/'NHD_delta_audit';out.mkdir(exist_ok=False);rows=[]
for name,cmd in [('proof1',['NHD_native/NHD_ProofDriver','proof1']),('scan',['NHD_native/NHD_ScanDriver','scan'])]:
 start=time.monotonic();log=out/(name+'.log');tim=out/(name+'.time.log');before=hashlib.sha256((B/cmd[0]).read_bytes()).hexdigest()
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text();stats=tim.read_text()
 def metric(label):return next((l.split(':',1)[1].strip() for l in stats.splitlines() if label in l),None)
 row=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),source_revision=parent['source_revision'],parent_attempt=parent['attempt'],same_optimized_binary_sha256=before,print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s),results=[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')])
 assert hashlib.sha256((B/cmd[0]).read_bytes()).hexdigest()==before
 (out/(name+'.json')).write_text(json.dumps(row,indent=1)+'\n');rows.append(row)
 print(json.dumps(dict(target=name,exit=r.returncode,wall_seconds=row['wall_seconds'],peak_rss_kib=row['peak_rss_kib'],roots=len(row['results']))),flush=True)
 if r.returncode:sys.exit(r.returncode)
 if name=='proof1':assert len(row['results'])==2 and all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in row['results'])
 else:
  scan=[json.loads(l) for l in (B/'NHD_LOADED_scan.jsonl').read_text().splitlines()]
  assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in scan)
  (out/'scan_summary.json').write_text(json.dumps(dict(modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),indent=1))
(out/'SUMMARY.json').write_text(json.dumps(dict(status='PASS',commands=rows,unchanged_fixture_attempt='NHD_L014',old_roots_reused=12,new_roots=2),indent=1)+'\n')
