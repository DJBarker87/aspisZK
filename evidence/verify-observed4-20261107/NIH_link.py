from pathlib import Path
import subprocess,time,re,hashlib,json,sys
B=Path.cwd();T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';results=[]
for name in ['NIH_ProofDriver','NIH_Driver']:
 cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NIH_native/'+name,'NIH_native/'+name+'.c','NIH_native/NFA_WALKER.c','NIH_native/NFA_MemoryLimit.c']
 start=time.monotonic()
 with (B/(name+'-link.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(B/(name+'-link.time')),*cmd],stdout=out,stderr=subprocess.STDOUT)
 timing=(B/(name+'-link.time')).read_text();metric=lambda key:re.search(re.escape(key)+r':\s*(.*)',timing)[1]
 p=B/'NIH_native'/name
 results.append(dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),binary_sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None,source_hashes={s:hashlib.sha256((B/s).read_bytes()).hexdigest() for s in cmd if s.endswith('.c')},print_axioms='N/A: optimized C linking'))
 (B/'NIH_LINK.json').write_text(json.dumps(results,indent=2)+'\n')
 if r.returncode:print((B/(name+'-link.log')).read_text());sys.exit(r.returncode)
print(json.dumps(results))
