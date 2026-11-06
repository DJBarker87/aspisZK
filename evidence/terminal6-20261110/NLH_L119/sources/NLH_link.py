from pathlib import Path
import json,hashlib,subprocess,time,re,shutil,os
b=Path.cwd();x=json.loads((b/'NLH_DRIVER_INPUTS.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();native=b/'NLH_native';native.mkdir(exist_ok=True)
for row in x['c_sources']:
 src=Path(row['source']);assert sha(src)==row['sha256'],str(src);shutil.copyfile(src,native/src.name)
raw=x['raw_driver'];assert sha(b/'NLH_ProofDriver.lean')==x['raw_source_sha256']==raw['source_sha256'];exe=Path(raw['binary']);assert sha(exe)==raw['binary_sha256'];shutil.copyfile(exe,native/'NLH_ProofDriver');(native/'NLH_ProofDriver').chmod(0o755)
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLH_native/NLH_Driver','NLH_native/NLH_Driver.c','NLH_native/NFA_WALKER.c','NLH_native/NFA_MemoryLimit.c']
start=time.monotonic()
with (b/'NLH_Driver-link.log').open('w')as f:r=subprocess.run(['/usr/bin/time','-v','-o','NLH_Driver-link.time',*cmd],stdout=f,stderr=subprocess.STDOUT)
t=(b/'NLH_Driver-link.time').read_text();row=dict(command=cmd,exit=r.returncode,wall=time.monotonic()-start,peak_rss_kib=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',t)[1],swap=re.search(r'Swaps:\s*(\d+)',t)[1],raw_driver_reused=raw,walker_identity=json.loads((b/'NLH_WALKER_IDENTITY.json').read_text()))
if r.returncode==0:row['binary_sha256']=sha(native/'NLH_Driver')
(b/'NLH_LINK.json').write_text(json.dumps(row,indent=1)+'\n');assert r.returncode==0
for suffix in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:(b/('NKI_'+suffix)).write_bytes((b/('NLH_'+suffix)).read_bytes())
print(json.dumps(dict(link_exit=r.returncode,optimized=True,raw_driver_byte_identical=True)))
