"""Bounded immutable export inventory + public package/static DSO analysis.
No target executable/compiler/Cargo/namespace/scope. Writes only own analysis-v1.
"""
import hashlib,json,os,pathlib,re,resource,stat,subprocess,sys,tarfile,time,traceback
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077)
P=pathlib.Path;S=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024')
PARENT=S/'SbfClosure-20261025-v1';O=PARENT/'analysis-v1';start=time.monotonic()
r=dict(command=['python3','-B','-c','literal SbfClosure_analyze_host.py via SSH'],print_axioms='N/A')
def pin(p):
 p=P(p);h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return dict(bytes=p.stat().st_size,sha256=h.hexdigest(),mode=stat.S_IMODE(p.stat().st_mode))
def verify_parent():
 for p in (S,PARENT):
  assert p.resolve()==p and p.stat().st_uid==1000 and stat.S_IMODE(p.stat().st_mode)==0o700
 assert (S/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
 assert (PARENT/'OWNER').read_text()=='SbfClosure 20261025\n'
 for p,h in {'source-inputs.json':'a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1','src/Cargo.lock':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','rustc-diagnostics.py':'fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'}.items():assert pin(S/p)['sha256']==h
 reservations=[];cg=P('/sys/fs/cgroup')
 def visit(p):
  if p!=cg and 'populated 1' not in (p/'cgroup.events').read_text():return
  cap=(p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
  if cap!='max':reservations.append((str(p),int(cap)));return
  for d in p.iterdir():
   if d.is_dir():visit(d)
 visit(cg);assert sum(x[1] for x in reservations)+536870912<55*1024**3
 return reservations
try:
 r['reservation_observation']=verify_parent();O.mkdir(mode=0o700)
 rows=[];seen=set();total=0
 prefixes=('evidence/sbf-inputs-20261024/','evidence/sbf-recapture-prep-20261024/','evidence/sbf-identity-20261024/','evidence/sbf-cache-prep-20261024/','tools/sbf-inputs-20261024/','tools/sbf-closure-20261025/','evidence/sbf-closure-20261025/Cargo189-','evidence/sbf-closure-20261025/REVISION')
 with tarfile.open(fileobj=sys.stdin.buffer,mode='r|') as tar:
  for m in tar:
   p=pathlib.PurePosixPath(m.name);assert not p.is_absolute() and '..' not in p.parts and str(p)==m.name.rstrip('/')
   if m.isdir():continue
   assert m.isfile() and m.name.startswith(prefixes) and m.name not in seen;seen.add(m.name)
   assert m.size<=5_000_000;total+=m.size;assert total<64*1024**2
   dest=O/m.name;dest.parent.mkdir(parents=True,exist_ok=True)
   with tar.extractfile(m) as src,dest.open('xb') as out:
    while b:=src.read(1024**2):out.write(b)
   assert dest.stat().st_size==m.size;rows.append(dict(path=m.name,**pin(dest)))
 r['exports']=rows
 sys.path.insert(0,str(O/'tools/sbf-closure-20261025'))
 import SbfClosure_receipt as receipt
 import SbfClosure_inventory as inv
 material=json.loads((O/'evidence/sbf-recapture-prep-20261024/materialized-files.json').read_text())
 manifest={x['path'].removeprefix('src/'):x for x in material}
 revision=(O/'evidence/sbf-closure-20261025/REVISION').read_bytes().strip()
 def gitview(*a):
  if a==('rev-parse','HEAD'):return revision+b'\n'
  if a[0]=='show':
   rev,path=a[1].split(':',1)
   if rev==inv.REV:
    assert path.startswith(prefixes);return (O/path).read_bytes()
   assert rev==inv.SRC and path in manifest
   p=S/'src'/path;assert p.resolve()==p and p.stat().st_size<=5_000_000
   b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==manifest[path]['sha256'];return b
  assert a[0]=='ls-tree' and a[1:3]==('-r','--name-only')
  if a[3]==inv.REV:allnames=[x['path'] for x in rows]
  else:assert a[3]==inv.SRC;allnames=list(manifest)
  names=sorted(p for p in allnames if any(p==q or p.startswith(q+'/') for q in a[4:]))
  return ('\n'.join(names)+'\n').encode()
 receipt.git=gitview;inv.git=gitview
 r['inventory_exit']=receipt.run('inventory.receipt.json',inv.main)
 # Public package candidates: exact installed public paths only. No /etc/home/run,
 # package conffiles, local site packages, user configuration or credentials.
 old=json.loads((PARENT/'receipt.json').read_text());readelf=old['tools']['readelf'];dpkg=old['tools']['dpkg-query']
 assert pin(readelf['resolved'])['sha256']==readelf['sha256']
 assert pin(dpkg['resolved'])['sha256']==dpkg['sha256']
 packages=['gcc-13','cpp-13','gcc-13-x86-64-linux-gnu','cpp-13-x86-64-linux-gnu','libgcc-13-dev','libc6-dev','linux-libc-dev','binutils-x86-64-linux-gnu','libpython3.12-stdlib','libpython3.12-minimal','python3.12-minimal']
 records=[];queries=[];unresolved=[];paths=set()
 for pkg in packages:
  cmd=[dpkg['resolved'],'--listfiles',pkg];t=time.monotonic();p=subprocess.run(cmd,capture_output=True,timeout=5,env={'PATH':'/usr/bin:/bin','LC_ALL':'C'})
  assert len(p.stdout)<1_000_000 and len(p.stderr)<10000
  queries.append(dict(package=pkg,command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr=p.stderr.decode()))
  if p.returncode:unresolved.append(pkg);continue
  for line in p.stdout.decode().splitlines():
   if not line.startswith(('/usr/bin/','/usr/lib/','/usr/include/','/lib/','/lib64/')):continue
   q=P(line)
   if q.is_symlink():
    records.append(dict(package=pkg,path=line,type='symlink',mode=stat.S_IMODE(q.lstat().st_mode),link=os.readlink(q),resolved=str(q.resolve())))
   elif q.is_file():
    if line not in paths:records.append(dict(package=pkg,path=line,type='regular',**pin(q)));paths.add(line)
   elif q.is_dir():records.append(dict(package=pkg,path=line,type='directory',mode=stat.S_IMODE(q.stat().st_mode)))
 # Recursive DT_NEEDED static closure for observed host executables and known
 # platform/outer driver roots. No ldd, no loader invocation, no target execution.
 seeds=[x['resolved'] for x in old['tools'].values() if x]
 seeds += ['/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc','/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/cargo','/home/dombarker/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo','/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf']
 search=['/lib/x86_64-linux-gnu','/usr/lib/x86_64-linux-gnu','/lib64','/usr/lib64','/usr/lib/gcc/x86_64-linux-gnu/13']
 done={};pending=list(seeds)
 while pending:
  p=P(pending.pop());assert p.is_file();p=p.resolve();path=str(p)
  if path in done:continue
  assert len(done)<256
  with p.open('rb') as f:magic=f.read(4)
  if magic!=b'\x7fELF':done[path]=dict(**pin(p),non_elf=True);continue
  cmd=[readelf['resolved'],'--wide','--program-headers','--dynamic',path];begin=time.monotonic();q=subprocess.run(cmd,capture_output=True,timeout=5,env={'PATH':'/usr/bin:/bin','LC_ALL':'C'})
  assert q.returncode==0 and len(q.stdout)<1_000_000
  text=q.stdout.decode();needed=re.findall(r'\(NEEDED\).*\[(.*?)\]',text)
  interpreter=re.findall(r'Requesting program interpreter: (.*?)\]',text)
  rpaths=re.findall(r'\((?:RUNPATH|RPATH)\).*\[(.*?)\]',text)
  dirs=[s.replace('${ORIGIN}',str(p.parent)).replace('$ORIGIN',str(p.parent)) for v in rpaths for s in v.split(':')]
  assert all(x.startswith('/') and '$' not in x for x in dirs)
  resolved={}
  for lib in needed:
   assert '/' not in lib
   found=next((P(d)/lib for d in dirs+search if (P(d)/lib).is_file()),None)
   if found is None:unresolved.append(dict(object=path,needed=lib));continue
   resolved[lib]=dict(logical=str(found),resolved=str(found.resolve()),**pin(found));pending.append(str(found))
  for loader in interpreter:pending.append(loader)
  done[path]=dict(**pin(p),command=cmd,exit=q.returncode,wall_seconds=time.monotonic()-begin,needed=needed,interpreter=interpreter,rpath=rpaths,resolved=resolved,stdout_sha256=hashlib.sha256(q.stdout).hexdigest())
 receipt.write('native-public-packages.json',dict(status='CANDIDATE PUBLIC SET; NOT PRIVATE SEALED COPY OR EXECUTED CLOSURE',queries=queries,files=records,unresolved=unresolved))
 receipt.write('static-dso-closure.json',dict(objects=done,unresolved=unresolved,limitations='DT_NEEDED only: dlopen, native compiler search paths, headers, crt/linker scripts and SDK scripts still require static source and future trace join. Search order is explicit candidate policy, not proven loader-equivalence. No ldd/target execution.'))
 r.update(exit=0 if r['inventory_exit']==0 else 1,outputs=[dict(path=str(p.relative_to(O)),**pin(p)) for p in (O/'evidence/sbf-closure-20261025').iterdir() if p.is_file()])
except Exception as e:r.update(exit=1,error=repr(e),traceback=traceback.format_exc(),partial_retained=True)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
r.update(wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,swap=u.ru_nswap+c.ru_nswap)
with (O/'analysis.receipt.json').open('x') as f:json.dump(r,f,sort_keys=True);f.write('\n')
print(json.dumps(r,sort_keys=True));sys.exit(r['exit'])
