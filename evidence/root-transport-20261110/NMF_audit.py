"""Own audit submission; validation, NFX scanner and raw ax2 walker unchanged."""
from NMF_formal import *
def audit(a,kind,target):
 env=json.loads((E/'NMF_ENV.json').read_text());T=env['LEAN_SYSROOT'];extra={}
 if kind=='link':
  r=ssh('python3',f"from pathlib import Path;print(Path({(B+'/NMF_native/')!r}+{target!r}+'.c').read_text(),end='')");assert r.returncode==0,r.stderr
  extra['NMF_native/'+target+'.c']=r.stdout
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NMF_native/'+n]=(E/'NMF_native'/n).read_text()
  cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMF_native/'+target,
   'NMF_native/'+target+'.c','NMF_native/NFA_WALKER.c','NMF_native/NFA_MemoryLimit.c']
 elif kind=='audit':
  for n in ['NMF_batch.py','NMF_AUDIT_ROOTS.json','NMF_EXPECTED_IMPORTS.jsonl']:
   extra[n]=(E/n).read_text()
  cmd=['python3','NMF_batch.py',target]
 else:raise ValueError(kind)
 return run(a,kind,target,cmd,extra)
if __name__=='__main__':
 r=audit(*sys.argv[1:]);sys.exit(r['exit_status'])
