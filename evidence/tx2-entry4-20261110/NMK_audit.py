"""Own audit submission; validation, NFX scanner and raw ax2 walker unchanged."""
from NMK_formal import *
def audit(a,kind,target):
 env=json.loads((E/'NMK_ENV.json').read_text());T=env['LEAN_SYSROOT'];extra={}
 pins=json.loads((E/'NMK_WALKER_PIN.json').read_text())
 check=ssh('python3',f"from pathlib import Path;import hashlib;roots={env['LEAN_PATH'].split(':')!r};p=next(Path(x)/'NFA_WALKER.olean' for x in roots if (Path(x)/'NFA_WALKER.olean').is_file());print(hashlib.sha256(p.read_bytes()).hexdigest())")
 assert check.returncode==0 and check.stdout.strip()==pins['selected_object_sha256'],'Selected walker object differs from retained canonical pin'
 if kind=='link':
  r=ssh('python3',f"from pathlib import Path;print(Path({(B+'/NMK_native/')!r}+{target!r}+'.c').read_text(),end='')");assert r.returncode==0,r.stderr
  extra['NMK_native/'+target+'.c']=r.stdout
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NMK_native/'+n]=lzma.decompress((E/'NMK_native'/(n+'.xz')).read_bytes()).decode()
  cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMK_native/'+target,
   'NMK_native/'+target+'.c','NMK_native/NFA_WALKER.c','NMK_native/NFA_MemoryLimit.c']
 elif kind=='audit':
  for n in ['NMK_batch.py','NMK_AUDIT_ROOTS.json','NMK_EXPECTED_IMPORTS.jsonl']:
   extra[n]=(E/n).read_text()
  cmd=['python3','NMK_batch.py',target]
 else:raise ValueError(kind)
 return run(a,kind,target,cmd,extra)
if __name__=='__main__':
 r=audit(*sys.argv[1:]);sys.exit(r['exit_status'])
