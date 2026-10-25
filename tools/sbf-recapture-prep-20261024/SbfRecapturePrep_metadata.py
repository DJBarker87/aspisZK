#!/usr/bin/env python3
"""Pin immutable reviewed inputs and comparison-runtime modules; no tools executed."""
import hashlib,json,pathlib,resource,subprocess,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-recapture-prep-20261024';t=time.monotonic();BASE='009b61e61bf52dba92c4fbefae79702a938f05b3'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,'tools/sbf-identity-20261024','evidence/sbf-identity-20261024','evidence/port24sbfmap-20261024','evidence/coordinator-20261024/manager-common-20261024.txt'],text=True).splitlines()
rows=[]
for p in paths:
 b=subprocess.check_output(['git','show',BASE+':'+p]);rows.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),classification='REUSED immutable reviewed metadata; no new proof/build/ELF validation'))
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -']
code=r'''
import sys,os,json,hashlib,tarfile,bz2,hashlib,urllib.request,resource,time,_bz2,_hashlib,_ssl,ssl
s=time.monotonic();pins=[]
for module in [tarfile,bz2,hashlib,urllib.request,_bz2,_hashlib,_ssl,ssl]:
 p=module.__file__;b=open(p,'rb').read();pins.append(dict(module=module.__name__,path=p,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
p=sys.executable;b=open(p,'rb').read();u=resource.getrusage(0)
print(json.dumps(dict(python=sys.version,executable=p,python_sha256=hashlib.sha256(b).hexdigest(),modules=pins,openssl=ssl.OPENSSL_VERSION,wall_seconds=time.monotonic()-s,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A',limitations='Pins comparison interpreter and direct stdlib/native extension modules. Not a full loaded-DSO/time-of-use identity closure. No compiler executed.')))
'''
x=subprocess.run(cmd,input=code.encode(),capture_output=True);assert x.returncode==0,x.stderr
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
r=dict(immutable_base=BASE,immutable_inputs=rows,comparison_runtime=json.loads(x.stdout),receipt=dict(command=['python3',str(T/'SbfRecapturePrep_metadata.py')],remote_command=cmd,remote_code_sha256=hashlib.sha256(code.encode()).hexdigest(),exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A'))
(E/'metadata-pins.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(immutable_inputs=len(rows),runtime_modules=len(r['comparison_runtime']['modules']),receipt=r['receipt']),indent=2))
