"""Run explicit recovered configurations sequentially in one admitted capped scope.
This is an owned extraction controller, not a replacement launcher/barrier.
"""
from pathlib import Path
import sys,os,json,time,subprocess,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;a=sys.argv[1];cfg=json.loads((E/(a+'.json')).read_text());spec=json.loads((E/(a+'_batch.json')).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'));cg=Path('/sys/fs/cgroup')/rel
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']};assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert len(spec['runs'])<=10
for run in spec['runs']:
 q=json.loads((E/(run+'_spec.json')).read_text());out=E/run;out.mkdir(exist_ok=False);start=time.monotonic();cmd=['python3','NML_extract.py',run]
 env=dict(os.environ,NML_BATCH_ATTEMPT=a)
 with (out/'stdout.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log')]+cmd,cwd=E,env=env,stdout=f,stderr=subprocess.STDOUT)
 timing=(out/'time.log').read_text();vals={k.strip():v.strip() for l in timing.splitlines() if ':' in l for k,v in [l.split(':',1)]}
 rc=dict(attempt=run,kind='extract',module=','.join(q['groups']),scope_attempt=a,scope_receipt=a+'/receipt.json',command=cmd,source_revision=cfg['source_revision'],source_tree_dirty=cfg.get('source_tree_dirty'),source_hashes={n:sha(E/n) for n in json.loads((E/(run+'.json')).read_text())['sources']},exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=vals.get('Maximum resident set size (kbytes)'),swaps=vals.get('Swaps'),limits=limits,cgroup=str(cg),print_axioms='N/A: extraction only',inherited_scope_timeout=180,configuration=q)
 (out/'configuration_receipt.json').write_text(json.dumps(rc,indent=2)+'\n')
 print(json.dumps(dict(attempt=run,scope=a,exit=r.returncode,wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'])),flush=True)
 # Independent configurations continue after ordinary tool errors; no failed shape is repeated.
 if r.returncode in [-9,137,124]:raise SystemExit(r.returncode)
print(json.dumps(dict(scope=a,configurations=len(spec['runs']),status='terminal')),flush=True)
