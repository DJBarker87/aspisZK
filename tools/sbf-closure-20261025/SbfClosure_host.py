"""One-shot bounded ordinary-user preparation. stdin is own tools-only tar.
No compiler, Cargo, namespace, scope, privilege, keys or global writes.
"""
import hashlib,json,os,pathlib,resource,stat,subprocess,sys,tarfile,time,traceback
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077)
P=pathlib.Path;S=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024')
O=S/'SbfClosure-20261025-v1'
t=time.monotonic();r={'command':['python3','-B','-c',P(__file__).name if '__file__' in globals() else 'literal SbfClosure_host.py via SSH'], 'print_axioms':'N/A','scope':'bounded Python preparation only; no build admission'}

def pin(p):
 p=P(p);h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return dict(bytes=p.stat().st_size,sha256=h.hexdigest(),mode=stat.S_IMODE(p.stat().st_mode),resolved=str(p.resolve()))
def checked(p):
 p=P(p)
 for q in (p,*p.parents):assert not q.is_symlink(),str(q)
 return p
try:
 assert os.getuid()==1000 and checked(S).resolve()==S
 assert S.stat().st_uid==1000 and stat.S_IMODE(S.stat().st_mode)==0o700
 assert checked(S/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
 pins={'source-inputs.json':'a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1','src/Cargo.lock':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','rustc-diagnostics.py':'fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'}
 for p,h in pins.items():assert pin(checked(S/p))['sha256']==h
 r['parent_pins']=pins
 reservations=[];cg=P('/sys/fs/cgroup')
 def visit(p):
  if p!=cg and 'populated 1' not in (p/'cgroup.events').read_text():return
  cap=(p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
  if cap!='max':reservations.append(dict(path=str(p),max=int(cap)));return
  for d in p.iterdir():
   if d.is_dir():visit(d)
 visit(cg)
 total=sum(x['max'] for x in reservations);assert total+536870912<55*1024**3
 r['reservation_observation']=dict(populated_topmost=reservations,total=total,preparation_limit=536870912,authority='not GO; bounded nonbuild metadata only')
 O.mkdir(mode=0o700);(O/'OWNER').write_text('SbfClosure 20261025\n')
 # Tools-only incoming archive; no arbitrary paths/links/hardlinks/special modes.
 names=set();incoming=[]
 with tarfile.open(fileobj=sys.stdin.buffer,mode='r|') as tar:
  for m in tar:
   p=pathlib.PurePosixPath(m.name);assert not p.is_absolute() and '..' not in p.parts
   assert p.parts[:2]==('tools','sbf-closure-20261025')
   assert str(p)==m.name.rstrip('/') and str(p) not in names;names.add(str(p))
   assert m.isdir() or m.isfile();assert m.size<=256000 and not m.mode&0o7000
   dest=O/str(p)
   if m.isdir():dest.mkdir(parents=True,exist_ok=True);continue
   assert p.name.startswith('SbfClosure_') and p.suffix in ('.py','.txt')
   dest.parent.mkdir(parents=True,exist_ok=True)
   with tar.extractfile(m) as src,dest.open('xb') as dst:dst.write(src.read(256001))
   assert dest.stat().st_size==m.size;incoming.append(dict(path=str(p),**pin(dest)))
 assert len(incoming)<=20
 r['helpers']=incoming
 # Test subprocess only: no Linux backend call; inherits 512MiB AS limit.
 (O/'evidence/sbf-closure-20261025').mkdir(parents=True)
 # Receipt git queries remain local to this stage: supply source revision via sealed marker.
 # Test only invokes rev-parse; shim avoids reading any other repository.
 tests=O/'tools/sbf-closure-20261025/SbfClosure_test.py'
 receipt=tests.with_name('SbfClosure_receipt.py')
 source=receipt.read_text();source=source.replace("return subprocess.check_output(['git', *args], cwd=ROOT)","assert args == ('rev-parse', 'HEAD'); return b'HOST-TEST-INPUTS-SEE-HELPER-HASHES\\n'")
 # Do not rewrite helper bytes: exec the small shim in memory then import test.
 shim="import sys,runpy;sys.path.insert(0,"+repr(str(tests.parent))+");import SbfClosure_receipt as r;r.git=lambda *a:b'HOST-TEST-INPUTS-SEE-HELPER-HASHES\\n';runpy.run_path("+repr(str(tests))+",run_name='__main__')"
 c=['/usr/bin/python3','-I','-B','-c',shim];begin=time.monotonic()
 p=subprocess.run(c,cwd=O,env={'PATH':'/usr/bin:/bin','LC_ALL':'C'},capture_output=True,timeout=20)
 r['tests']=dict(command=c,exit=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),wall_seconds=time.monotonic()-begin)
 # Exact public executable pins and static loader/DT_NEEDED evidence. NEVER execute target.
 tools={};dynamic={}
 for name in ('readelf','strace','setpriv','chroot','mount','unshare','python3','gcc','cc','as','ar','ld','env','sh','dpkg-query'):
  candidates=[P(d)/name for d in ('/usr/bin','/bin','/usr/sbin','/sbin')]
  found=next((x for x in candidates if x.is_file()),None)
  tools[name]=None if found is None else dict(path=str(found),**pin(found))
 readelf=tools['readelf'];assert readelf is not None
 for name,info in tools.items():
  if info is None:continue
  cmd=[readelf['path'],'--wide','--file-header','--program-headers','--dynamic',info['resolved']]
  q=subprocess.run(cmd,capture_output=True,timeout=5,env={'PATH':'/usr/bin:/bin','LC_ALL':'C'})
  assert len(q.stdout)<1000000 and len(q.stderr)<10000
  dynamic[name]=dict(command=cmd,exit=q.returncode,stdout=q.stdout.decode(),stderr=q.stderr.decode(),assessment='static ELF data only; not recursive closure or tool execution')
 r['tools']=tools;r['static_elf']=dynamic
 r['runtime']=dict(interpreter=pin(P(sys.executable).resolve()),version=sys.version,modules={str(P(m.__file__).resolve()):pin(P(m.__file__).resolve()) for m in list(sys.modules.values()) if getattr(m,'__file__',None) and P(m.__file__).is_file()})
 r['exit']=0 if p.returncode==0 else 1
except Exception as e:r.update(exit=1,error=repr(e),traceback=traceback.format_exc(),partial_retained=True)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
r.update(wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,swap=u.ru_nswap+c.ru_nswap)
if O.exists():
 with (O/'receipt.json').open('x') as f:json.dump(r,f,sort_keys=True);f.write('\n')
print(json.dumps(r,sort_keys=True));sys.exit(r['exit'])
