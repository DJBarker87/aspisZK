from pathlib import Path
import subprocess,time,re,hashlib,json,sys
B=Path.cwd();T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';results=[]
import shutil
prior=Path('/home/dombarker/project-offloads/codex-cx-verify-observed7-20261108/NJM_native')
for name,h in {'NFA_WALKER.c': 'c041aabaccba69e3775f0e23a03c553968a05ec89f39e86bb830731ed1ec2420', 'NFA_MemoryLimit.c': '732e02a205527ff227b0fc5a4dba2e9a9456dae0eb85688601b4ef0515b0fc4d'}.items():
 p=prior/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 shutil.copyfile(p,B/'NJT_native'/name)
for name in ['NJT_ProofDriver','NJT_Driver']:
 cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJT_native/'+name,'NJT_native/'+name+'.c','NJT_native/NFA_WALKER.c','NJT_native/NFA_MemoryLimit.c']
 start=time.monotonic()
 with (B/(name+'-link.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(B/(name+'-link.time')),*cmd],stdout=out,stderr=subprocess.STDOUT)
 timing=(B/(name+'-link.time')).read_text();metric=lambda key:re.search(re.escape(key)+r':\s*(.*)',timing)[1]
 p=B/'NJT_native'/name
 results.append(dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),binary_sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None,source_hashes={s:hashlib.sha256((B/s).read_bytes()).hexdigest() for s in cmd if s.endswith('.c')},print_axioms='N/A: optimized C linking'))
 (B/'NJT_LINK.json').write_text(json.dumps(results,indent=2)+'\n')
 if r.returncode:print((B/(name+'-link.log')).read_text());sys.exit(r.returncode)
print('NJT optimized audit drivers linked')
