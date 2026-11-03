"""Final aggregate payload, invoked by the unchanged lead-owned agg16 runner."""
import hashlib,json,os,subprocess,sys,time
from pathlib import Path
B=Path(__file__).resolve().parent
rows=json.loads((B/sys.argv[1]).read_text())
out=B/sys.argv[2];out.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=os.environ['LEAN_PATH'].split(':')
pins=[json.loads(line) for line in (B/'NER_PREAGG_OBJECTS.jsonl').read_text().splitlines()]
def verify_pins():
 for module in pins:
  for artifact in module['artifacts']:
   assert sha(Path(artifact['path']))==artifact['sha256'],artifact['path']
verify_pins()
print('NER_PREAGG_PINS_VERIFIED',flush=True)
for row in rows:
 m=row['module']; src=B/(m.replace('.','/')+'.lean');obj=src.with_suffix('.olean')
 assert sha(src)==row['source_sha256'],m
 deps={}
 for dep in row['cohort_imports']:
  p=next(Path(root)/(dep.replace('.','/')+'.olean') for root in paths if (Path(root)/(dep.replace('.','/')+'.olean')).exists())
  deps[dep]={'path':str(p),'sha256':sha(p)}
 cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M15000','-DElab.async=false','-o',str(obj),str(src)]
 start=time.monotonic()
 with (out/(m+'.log')).open('w') as f:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(out/(m+'.time')),'timeout','600',*cmd],stdout=f,stderr=subprocess.STDOUT)
 log=(out/(m+'.log')).read_text();tim=(out/(m+'.time')).read_text()
 def metric(n):return next((l.split(':',1)[1].strip() for l in tim.splitlines() if n in l),None)
 receipt={**row,'command':cmd,'exit_status':r.returncode,'wall_seconds':time.monotonic()-start,'peak_rss_kib':metric('Maximum resident set size'),'swaps':metric('Swaps'),'selected_imports':deps,'object_sha256':sha(obj) if r.returncode==0 else None,'print_axioms':[l for l in log.splitlines() if 'depends on axioms:' in l or 'does not depend on any axioms' in l]}
 with (out/'modules.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(json.dumps({'module':m,'exit':r.returncode,'wall':receipt['wall_seconds']}),flush=True)
 if r.returncode:sys.exit(r.returncode)

# The aggregate compilation has completed and released its import environment.
# The standalone driver now loads that exact object cohort in one private view.
cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M15000','-DElab.async=false','--run','NER_FinalDriver.lean','final']
r=subprocess.run(cmd)
verify_pins()
print('NER_POSTAGG_INPUTS_UNCHANGED',flush=True)
sys.exit(r.returncode)
