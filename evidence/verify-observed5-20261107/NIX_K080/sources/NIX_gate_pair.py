"""Two separately validated capped-scope children, one positive and one matched control.
No validation is cached between Kani invocations. A timeout never yields credit.
"""
from pathlib import Path
import subprocess,json,re,time,hashlib,sys
B=Path.cwd();x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];rows=[]
for i,phase in enumerate(['positive','negative']):
 y=dict(x);y['attempt']=a+'_'+phase;y['native_command']=x['native_commands'][i];y.pop('native_commands');p=B/(y['attempt']+'.json');p.write_text(json.dumps(y,indent=2)+'\n')
 start=time.monotonic();log=B/(y['attempt']+'.log');timing=B/(y['attempt']+'.time')
 with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(timing),'python3','NIX_gate.py',p.name],stdout=f,stderr=subprocess.STDOUT)
 text=log.read_text();t=timing.read_text();metric=lambda key:(m[1] if (m:=re.search(re.escape(key)+r':\s*(.*)',t)) else None)
 semantic_control='VERIFICATION:- FAILED' in text and not any(k in text.lower() for k in ['unwinding assertion','unwinding failures','cbmc timed out'])
 passed=(r.returncode==0 and 'VERIFICATION:- SUCCESSFUL'in text) if phase=='positive' else (r.returncode!=0 and semantic_control)
 rows.append(dict(phase=phase,target=y['native_command'],exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),expected_verdict=passed,stdout_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),print_axioms='N/A: native assertion'))
 print(json.dumps(rows[-1]),flush=True)
(B/(a+'_PAIR.json')).write_text(json.dumps(dict(children=rows,passed=all(r['expected_verdict'] for r in rows),source_revision=x['source_revision'],kind='one positive and one matched negative, separately revalidated before EACH Kani invocation'),indent=2)+'\n')
sys.exit(0 if all(r['expected_verdict'] for r in rows) else 1)
