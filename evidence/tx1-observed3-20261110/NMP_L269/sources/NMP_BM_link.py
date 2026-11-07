from pathlib import Path
import json,hashlib,subprocess,sys
B=Path.cwd();name=sys.argv[1];assert name in ['NMP_BM_Driver','NMP_BM_ProofDriver']
cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NMP_native/'+name,'NMP_native/'+name+'.c','NMP_native/NFA_WALKER.c','NMP_native/NFA_MemoryLimit.c']
r=subprocess.run(cmd);assert r.returncode==0,r.returncode
p=B/'NMP_native'/name
(B/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(command=cmd,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size),indent=2))
print('Linked optimized '+name)
