from pathlib import Path
import json,hashlib,subprocess,time,sys,re
exec((Path.cwd()/'NKR_gate_setup.py').read_text())
b=Path.cwd();rows=[];T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
for row in json.loads((b/'NKR_GATE_PINS.json').read_text()):assert hashlib.sha256(Path(row['target']).read_bytes()).hexdigest()==row['sha256']
for name in ['NKR_Driver']:
 cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKR_native/'+name,'NKR_native/'+name+'.c','NKR_native/NFA_WALKER.c','NKR_native/NFA_MemoryLimit.c'];start=time.monotonic();log=b/(name+'-link.log');timing=b/(name+'-link.time')
 with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],stdout=f,stderr=subprocess.STDOUT)
 t=timing.read_text();rows.append(dict(target=name,command=cmd,exit=r.returncode,wall=time.monotonic()-start,peak_rss_kib=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',t)[1],swap=re.search(r'Swaps:\s*(\d+)',t)[1],sha256=hashlib.sha256((b/'NKR_native'/name).read_bytes()).hexdigest()if r.returncode==0 else None))
 if r.returncode:break
(b/'NKR_LINK.json').write_text(json.dumps(rows,indent=1));print(json.dumps(rows))
assert r.returncode==0

# Reuse the byte-identical admitted raw driver; only runtime input/root lists change.
import shutil
origin=Path('/home/dombarker/project-offloads/codex-cx-terminal4-20261108')
old=json.loads((origin/'NKI_LINK.json').read_text());pin=next(x for x in old if x['target']=='NKI_ProofDriver')
exe=origin/'NKI_native/NKI_ProofDriver';assert hashlib.sha256(exe.read_bytes()).hexdigest()==pin['sha256']
assert (b/'NKR_ProofDriver.lean').read_bytes()==(origin/'NKI_ProofDriver.lean').read_bytes()
shutil.copyfile(exe,b/'NKR_native/NKR_ProofDriver');(b/'NKR_native/NKR_ProofDriver').chmod(0o755)
for suffix in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:
 shutil.copyfile(b/('NKR_'+suffix),b/('NKI_'+suffix))
(b/'NKR_PROOF_DRIVER_REUSE.json').write_text(json.dumps(dict(source=str(origin/'NKI_ProofDriver.lean'),source_sha256=hashlib.sha256((b/'NKR_ProofDriver.lean').read_bytes()).hexdigest(),binary=str(exe),binary_sha256=pin['sha256'],unchanged=True,runtime_aliases=['NKI_AUDIT_ROOTS.json','NKI_AUDIT_MODULES.json'],reason='Exact unchanged driver/cache reuse under AGENTS resourcepolicy; new root/module lists only')));print('Pinned unchanged raw driver reused; no redundant compile/link')
