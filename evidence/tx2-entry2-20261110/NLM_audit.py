"""Own audit submission; validation, NFX scanner and raw ax2 walker unchanged."""
from NLM_formal import *
def audit(a,kind,target):
 env=json.loads((E/'NLM_ENV.json').read_text());T=env['LEAN_SYSROOT'];extra={}
 if kind=='link':
  r=ssh('python3',f"from pathlib import Path;print(Path({(B+'/NLM_native/')!r}+{target!r}+'.c').read_text(),end='')");assert r.returncode==0,r.stderr
  extra['NLM_native/'+target+'.c']=r.stdout
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NLM_native/'+n]=(E.parent/'tx2-entry-20261109'/'NLE_native'/n).read_text()
  cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLM_native/'+target,
   'NLM_native/'+target+'.c','NLM_native/NFA_WALKER.c','NLM_native/NFA_MemoryLimit.c']
 elif kind=='audit':
  for n in ['NLM_batch.py','NLM_AUDIT_ROOTS.json','NLM_EXPECTED_IMPORTS.jsonl']:
   extra[n]=(E/n).read_text()
  cmd=['python3','NLM_batch.py',target]
 else:raise ValueError(kind)
 return run(a,kind,target,cmd,extra)
if __name__=='__main__':
 r=audit(*sys.argv[1:]);sys.exit(r['exit_status'])
