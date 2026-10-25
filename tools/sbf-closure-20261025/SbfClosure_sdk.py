"""Focused correction: actual reviewed platform-tools-sdk/sbf, not sdk/sbf."""
import hashlib,json,os,pathlib,resource,stat,sys,time,traceback
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077)
P=pathlib.Path;B=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfClosure-20261025-v1');t=time.monotonic();r=dict(command=['python3','-B','-c','literal SbfClosure_sdk.py via SSH'],print_axioms='N/A')
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return dict(bytes=p.stat().st_size,sha256=h.hexdigest(),mode=stat.S_IMODE(p.stat().st_mode))
try:
 assert B.resolve()==B and B.stat().st_uid==1000 and stat.S_IMODE(B.stat().st_mode)==0o700 and (B/'OWNER').read_text()=='SbfClosure 20261025\n'
 cg=P('/sys/fs/cgroup');reservations=[]
 def visit(p):
  if p!=cg and 'populated 1' not in (p/'cgroup.events').read_text():return
  cap=(p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
  if cap!='max':reservations.append((str(p),int(cap)));return
  for q in p.iterdir():
   if q.is_dir():visit(q)
 visit(cg);assert sum(x[1] for x in reservations)+536870912<55*1024**3;r['reservations']=reservations
 release=P('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin')
 assert pin(release/'cargo-build-sbf')['sha256']=='46e50d5d1bcc70abfd74f0b6281071ef91576031330d1d892622e1ea59445d6c'
 sdk=release/'platform-tools-sdk/sbf';assert sdk.is_dir() and sdk.resolve()==sdk
 rows=[];texts=[]
 for root,ds,fs in os.walk(sdk,followlinks=False):
  assert len(rows)<10000
  for name in sorted(ds+fs):
   p=P(root)/name;row=dict(path=str(p),mode=stat.S_IMODE(p.lstat().st_mode))
   if p.is_symlink():
    target=os.readlink(p);resolved=str(p.resolve())
    assert resolved.startswith(str(sdk)+'/') or resolved.startswith('/home/dombarker/.cache/solana/v1.52/platform-tools'),resolved
    row.update(type='symlink',link=target,resolved=resolved)
   elif p.is_dir():row['type']='directory'
   elif p.is_file():
    row.update(type='regular',**pin(p))
    if p.suffix in ('.sh','.py') and p.stat().st_size<100000:texts.append(dict(path=str(p),text=p.read_text(),**pin(p)))
   else:raise ValueError('special SDK input')
   rows.append(row)
 r.update(exit=0,files=rows,scripts=texts,claim='Exact current SDK finite candidate set, no execution/private copy/TOU or archive association',old_failure='public-finish looked at absent bin/sdk/sbf; source corrected using immutable current-global symlink record; no speculative filesystem search')
except Exception as e:r.update(exit=1,error=repr(e),traceback=traceback.format_exc())
u=resource.getrusage(0);r.update(wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap)
b=(json.dumps(r,sort_keys=True)+'\n').encode();assert len(b)<5000000
with (B/'sdk-v1.json').open('xb') as f:f.write(b)
print(b.decode());sys.exit(r['exit'])
