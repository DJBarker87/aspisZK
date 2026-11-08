from pathlib import Path
import json,hashlib,subprocess,sys,lzma
B=Path.cwd();name=sys.argv[1];assert name in ['NNG_Resume_Driver','NNG_Resume_ProofDriver']
cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NNG_native/'+name,'NNG_native/'+name+'.c','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']
r=subprocess.run(cmd);assert r.returncode==0,r.returncode
p=B/'NNG_native'/name
(B/(name+'_BINARY_PIN.json')).write_text(json.dumps(dict(command=cmd,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size),indent=2))
print('Linked optimized '+name)

source=B/'NNG_native'/(name+'.c')
data=source.read_bytes()
(B/(name+'.c.xz')).write_bytes(lzma.compress(data,preset=6))
(B/(name+'.c.sha256')).write_text(hashlib.sha256(data).hexdigest()+'\n')

pin_path=B/(name+'_BINARY_PIN.json')
pin=json.loads(pin_path.read_text())
pin['c_inputs']={str(q):{'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size} for q in [source,B/'NNG_native/NFA_WALKER.c',B/'NNG_native/NFA_MemoryLimit.c']}
pin_path.write_text(json.dumps(pin,indent=2))
