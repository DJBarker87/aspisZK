from pathlib import Path
import subprocess,hashlib,json
B=Path.cwd();T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
rows=[]
for name in ['Driver','ProofDriver']:
 n='NLV_native/NLV_'+name;cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o',n,n+'.c','NLV_native/NFA_WALKER.c','NLV_native/NFA_MemoryLimit.c'];subprocess.run(cmd,check=True)
 p=B/n;rows.append(dict(target=n,command=cmd,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(B/'NLV_AUDIT_BINARY_PINS.json').write_text(json.dumps(rows,indent=2));print('Linked optimized unchanged ax2/NFX drivers')
