from pathlib import Path
import json,hashlib,subprocess,time,sys,re
b=Path.cwd();rows=[];T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for row in json.loads((b/'NJX_GATE_PINS.json').read_text()):assert hashlib.sha256(Path(row['target']).read_bytes()).hexdigest()==row['sha256']
for name in ['NJX_Driver','NJX_ProofDriver']:
 cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJX_native/'+name,'NJX_native/'+name+'.c','NJX_native/NFA_WALKER.c','NJX_native/NFA_MemoryLimit.c'];start=time.monotonic();log=b/(name+'-link.log');timing=b/(name+'-link.time')
 with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],stdout=f,stderr=subprocess.STDOUT)
 t=timing.read_text();rows.append(dict(target=name,command=cmd,exit=r.returncode,wall=time.monotonic()-start,peak_rss_kib=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',t)[1],swap=re.search(r'Swaps:\s*(\d+)',t)[1],sha256=hashlib.sha256((b/'NJX_native'/name).read_bytes()).hexdigest()if r.returncode==0 else None))
 if r.returncode:break
(b/'NJX_LINK.json').write_text(json.dumps(rows,indent=1));print(json.dumps(rows));sys.exit(r.returncode)
