"""Own-root raw ax2 audit only; unchanged NFA walker and memory shim."""
from NNC_formal import *
def audit(a,kind,target):
 env=json.loads((E/'NNC_ENV.json').read_text());T=env['LEAN_SYSROOT'];extra={}
 if kind=='link':
  r=ssh('python3',f"from pathlib import Path;print(Path({(B+'/NNC_native/')!r}+{target!r}+'.c').read_text(),end='')");assert r.returncode==0,r.stderr
  extra['NNC_native/'+target+'.c']=r.stdout
  for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
   extra['NNC_native/'+n]=lzma.decompress((E/'NNC_native'/(n+'.xz')).read_bytes()).decode()
  cmd=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNC_native/'+target,
   'NNC_native/'+target+'.c','NNC_native/NFA_WALKER.c','NNC_native/NFA_MemoryLimit.c']
 elif kind=='audit':
  if target.startswith('batch') and int(target[5:])>=8:
   r=ssh('python3',f"from pathlib import Path;import hashlib,json;b=Path({B!r});files=[b/'NNC_native/NNC_OptionBDriver']+sorted((b/'NNC_objects').glob('*.olean'));print(json.dumps({{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}))");assert r.returncode==0,r.stderr
   extra['NNC_AUDIT_RUNTIME_PINS.json']=r.stdout
   (E/'NNC_AUDIT_RUNTIME_PINS.json').write_text(r.stdout)
  for n in ['NNC_batch.py','NNC_AUDIT_ROOTS.json']:extra[n]=(E/n).read_text()
  cmd=['python3','NNC_batch.py',target]
 else:raise ValueError(kind)
 return run(a,kind,target,cmd,extra)
if __name__=='__main__':
 r=audit(*sys.argv[1:]);sys.exit(r['exit_status'])
