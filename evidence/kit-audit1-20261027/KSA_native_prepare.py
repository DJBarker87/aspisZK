from pathlib import Path,PurePosixPath
import subprocess,tomllib,json,hashlib,posixpath
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027'
get=lambda p:subprocess.check_output(['git','show',rev+':'+p])
root=tomllib.loads(get('Cargo.toml').decode());dirs=set();todo=list(root['workspace']['members'])
while todo:
 p=posixpath.normpath(todo.pop())
 if p in dirs:continue
 dirs.add(p);v=tomllib.loads(get(p+'/Cargo.toml').decode())
 def walk(x):
  if isinstance(x,dict):
   for k,z in x.items():
    if k.endswith('dependencies') and isinstance(z,dict):
     for dep in z.values():
      if isinstance(dep,dict) and 'path' in dep:todo.append(posixpath.normpath(p+'/'+dep['path']))
    elif isinstance(z,(dict,list)):walk(z)
  elif isinstance(x,list):
   for z in x:walk(z)
 walk(v)
paths=['Cargo.toml','Cargo.lock']+sorted(dirs)
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'--']+paths,text=True).splitlines()
manifest=[dict(path=p,sha256=hashlib.sha256(get(p)).hexdigest()) for p in tracked]
(E/'KSA_native_sources.json').write_text(json.dumps(dict(revision=rev,paths=paths,files=manifest,wrapper_only='append cfg(test) module to crates/aspis-core/src/lib.rs'),indent=2)+'\n')
# Admission must have been recorded before this transfer; no proof process is submitted here.
assert json.loads((E/'KSA_R001-reservation.json').read_text())['allowed']
subprocess.run(['ssh',H,'mkdir -p '+B+'/KSA_src'],check=True)
p=subprocess.Popen(['git','archive',rev,'--']+paths,stdout=subprocess.PIPE)
r=subprocess.run(['ssh',H,'tar -xf - -C '+B+'/KSA_src'],stdin=p.stdout);p.stdout.close();assert p.wait()==0 and r.returncode==0
for name in ['KSA_native.py','KSA_native_test.rs']:
 subprocess.run(['scp','-q',str(E/name),H+':'+B+'/'+name],check=True)
subprocess.run(['ssh',H,'cat '+B+'/KSA_native_test.rs >> '+B+'/KSA_src/crates/aspis-core/src/lib.rs'],check=True)
print('frozen files',len(tracked))
