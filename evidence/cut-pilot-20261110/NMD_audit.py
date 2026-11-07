"""Own audit submission; validation, NFX scanner and raw ax2 walker unchanged."""
from NMD_formal import *
def audit(a,kind,target):
 env=json.loads((E/'NMD_ENV.json').read_text());T=env['LEAN_SYSROOT'];extra={}
 if kind=='link':
  r=ssh('python3',f"from pathlib import Path;print(Path({(B+'/NMD_native/')!r}+{target!r}+'.c').read_text(),end='')");assert r.returncode==0,r.stderr
  extra['NMD_native/'+target+'.c']=r.stdout
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NMD_native/'+n]=subprocess.check_output(['git','show','HEAD:evidence/tx2-entry-20261109/NLE_native/'+n],text=True)
  cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMD_native/'+target,
   'NMD_native/'+target+'.c','NMD_native/NFA_WALKER.c','NMD_native/NFA_MemoryLimit.c']
 elif kind=='audit':
  for n in ['NMD_batch.py','NMD_AUDIT_ROOTS.json','NMD_EXPECTED_IMPORTS.jsonl']:
   extra[n]=(E/n).read_text()
  cmd=['python3','NMD_batch.py',target]
 else:raise ValueError(kind)
 return run(a,kind,target,cmd,extra)
if __name__=='__main__':
 r=audit(*sys.argv[1:]);sys.exit(r['exit_status'])
