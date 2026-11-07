from pathlib import Path
import json,hashlib,subprocess,sys
B=Path.cwd();name=sys.argv[1];assert name in ['NNG_C087_Driver','NNG_C087_ProofDriver']
cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NNG_native/'+name,'NNG_native/'+name+'.c','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']
r=subprocess.run(cmd);assert r.returncode==0,r.returncode
p=B/'NNG_native'/name
(B/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(command=cmd,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size),indent=2))
print('Linked optimized '+name)
