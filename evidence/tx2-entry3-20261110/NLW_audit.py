"""Own audit submission; validation, NFX scanner and raw ax2 walker unchanged."""
from NLW_formal import *
def audit(a,kind,target):
 env=json.loads((E/'NLW_ENV.json').read_text());T=env['LEAN_SYSROOT'];extra={}
 if kind=='link':
  r=ssh('python3',f"from pathlib import Path;print(Path({(B+'/NLW_native/')!r}+{target!r}+'.c').read_text(),end='')");assert r.returncode==0,r.stderr
  extra['NLW_native/'+target+'.c']=r.stdout
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NLW_native/'+n]=(E.parent/'tx2-entry-20261109'/'NLE_native'/n).read_text()
  cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLW_native/'+target,
   'NLW_native/'+target+'.c','NLW_native/NFA_WALKER.c','NLW_native/NFA_MemoryLimit.c']
 elif kind=='audit':
  for n in ['NLW_batch.py','NLW_AUDIT_ROOTS.json','NLW_EXPECTED_IMPORTS.jsonl']:
   extra[n]=(E/n).read_text()
  cmd=['python3','NLW_batch.py',target]
 else:raise ValueError(kind)
 return run(a,kind,target,cmd,extra)
if __name__=='__main__':
 r=audit(*sys.argv[1:]);sys.exit(r['exit_status'])
