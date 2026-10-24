#!/usr/bin/env python3
"""Host Python-only archive preparation. No subprocesses, compilers or global writes."""
import hashlib,json,os,pathlib,re,resource,shutil,stat,sys,tarfile,time,tomllib,traceback
P=pathlib.Path
STAGE=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024')
OUT=STAGE/'SbfInputs-20261024'
LIMIT=512*1024**2

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def no_links(p):
 for q in (p,*p.parents):assert not q.is_symlink(),str(q)
def member_path(m,crate):
 s=m.name; p=pathlib.PurePosixPath(s)
 assert s and not p.is_absolute() and '..' not in p.parts and '\\' not in s
 assert p.parts[0]==crate and str(p)==s.rstrip('/'),s
 assert m.isfile() or m.isdir(),'link/special member: '+s
 assert not m.mode & ~0o777,'special mode: '+s
 assert m.size>=0 and m.size<=128*1024**2
 assert p.name not in ('.cargo-ok','.cargo-checksum.json'),'unexpected generated metadata'
 assert not (re.search(r'(keypair|private.?key|mnemonic|credential|secret|\.pem$|\.key$|\.env(?:\.|$)|id_rsa)',p.name,re.I) and p.suffix not in ('.rs','.toml','.md','.txt')),'possible key filename'
 return str(p)
def copy_file(src,dst,expected=None):
 no_links(src);s=src.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
 dst.parent.mkdir(parents=True,exist_ok=True)
 h=hashlib.sha256()
 with src.open('rb') as a,dst.open('xb') as b:
  while data:=a.read(1024**2):h.update(data);b.write(data)
 after=src.stat();assert all(getattr(after,k)==getattr(s,k) for k in ('st_dev','st_ino','st_size','st_mtime_ns','st_ctime_ns','st_mode','st_nlink')),'source metadata changed'
 os.chmod(dst,stat.S_IMODE(s.st_mode));assert digest(dst)==h.hexdigest()
 if expected:assert h.hexdigest()==expected
 return dict(bytes=s.st_size,sha256=h.hexdigest(),mode=oct(stat.S_IMODE(s.st_mode)))
def main():
 resource.setrlimit(resource.RLIMIT_AS,(LIMIT,LIMIT));os.umask(0o077)
 start=time.monotonic();receipt=dict(command=[sys.executable,'-B','-'],print_axioms='N/A: no theorem/compiler execution',address_space_limit_bytes=LIMIT)
 try:
  req=json.loads(sys.stdin.readline());receipt.update(source_revision=req['revision'],helper_sha256=req['helper_sha256'],request_sha256=req['request_sha256'],command=req['host_command'])
  no_links(STAGE);assert STAGE.resolve()==STAGE and STAGE.stat().st_uid==os.getuid()==1000 and stat.S_IMODE(STAGE.stat().st_mode)==0o700
  assert (STAGE/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
  pins={'source-inputs.json':'a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1','src/Cargo.lock':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','rustc-diagnostics.py':'fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'}
  for name,sha in pins.items():no_links(STAGE/name);assert digest(STAGE/name)==sha
  receipt['input_pins']=pins
  lock=tomllib.loads((STAGE/'src/Cargo.lock').read_text());locked={(p['name'],p['version']):p for p in lock['package']}
  packages=req['packages'];assert len(packages)==123 and len({p['crate'] for p in packages})==123
  for p in packages:
   assert re.fullmatch('[a-zA-Z0-9_.+-]+',p['crate']) and p['index']=='index.crates.io-1949cf8c6b5b557f'
   name,version=p['crate'].rsplit('-',1);l=locked[(name,version)]
   assert l['checksum']==p['archive_sha256']==p['lock_checksum'] and l['source']=='registry+https://github.com/rust-lang/crates.io-index'
  # Disjoint topmost finite populated cgroups: reservation observation only.
  reservations=[];cg=P('/sys/fs/cgroup')
  def visit(root):
   events={'populated':'1'} if root==cg else dict(line.split() for line in (root/'cgroup.events').read_text().splitlines())
   if events.get('populated')!='1':return
   cap=(root/'memory.max').read_text().strip() if (root/'memory.max').exists() else 'max'
   if cap!='max':
    reservations.append(dict(path=str(root),memory_max=int(cap)));return
   for q in root.iterdir():
    if q.is_dir():visit(q)
  visit(cg)
  reserve=sum(r['memory_max'] for r in reservations)
  receipt['preparation_reservations']=dict(disjoint=reservations,bytes=reserve,proposed_python_address_space=LIMIT,authority='observation for bounded preparation only; not build GO')
  assert reserve+LIMIT<55*1024**3
  mem=dict((a.rstrip(':'),int(b.split()[0])*1024) for a,b in (line.split(':',1) for line in P('/proc/meminfo').read_text().splitlines()))
  assert mem['MemAvailable']>7*1024**3+LIMIT
  assert shutil.disk_usage(STAGE).free>2*1024**3
  OUT.mkdir(mode=0o700);(OUT/'OWNER').write_text('SbfInputs 20261024\n')
  for n in ('target-verifier','target-pool','captures','tmp'): (OUT/n).mkdir(mode=0o700)
  result=[];files=0;total=0
  manifest=OUT/'registry-files.jsonl'
  with manifest.open('x') as mf:
   def record(p,kind,**kw):
    nonlocal files,total
    row=dict(path=str(p.relative_to(OUT)),type=kind,mode=oct(stat.S_IMODE(p.lstat().st_mode)),**kw)
    if kind=='regular':files+=1;total+=kw['bytes']
    mf.write(json.dumps(row,sort_keys=True)+'\n')
   for pkg in packages:
    crate=pkg['crate'];idx=pkg['index'];a=P('/home/dombarker/.cargo/registry/cache')/idx/(crate+'.crate')
    dest=OUT/'cargo/registry/cache'/idx/a.name
    arc=copy_file(a,dest,pkg['archive_sha256']);assert arc['bytes']==pkg['archive_bytes'];record(dest,'regular',bytes=arc['bytes'],sha256=arc['sha256'])
    src=OUT/'cargo/registry/src'/idx/crate;src.mkdir(parents=True)
    expected=set();directories={src};members_seen=set();member_bytes=0
    with tarfile.open(dest,'r:gz') as tar:
     members=tar.getmembers();assert len(members)<20000
     for m in members:
      name=member_path(m,crate);assert name not in members_seen,'duplicate member';members_seen.add(name)
      member_bytes+=m.size;assert member_bytes<=512*1024**2
     for m in members:
      rel=pathlib.PurePosixPath(m.name).relative_to(crate);p=src/str(rel)
      if m.isdir():p.mkdir(parents=True,exist_ok=True);directories.add(p);continue
      assert str(rel)!='.';p.parent.mkdir(parents=True,exist_ok=True)
      h=hashlib.sha256();n=0
      with tar.extractfile(m) as f,p.open('xb') as w:
       while b:=f.read(1024**2):w.write(b);h.update(b);n+=len(b)
      assert n==m.size;os.chmod(p,m.mode);assert digest(p)==h.hexdigest();expected.add(str(rel))
      record(p,'regular',bytes=n,sha256=h.hexdigest(),archive_mode=oct(m.mode))
     # Published directory modes, if present, applied after descendants exist.
     for m in members:
      if m.isdir():os.chmod(src/str(pathlib.PurePosixPath(m.name).relative_to(crate)),m.mode)
    # Selected official Cargo 1.89 registry/mod.rs LockMetadata v1 completion only.
    marker=src/'.cargo-ok';marker.write_bytes(b'{"v":1}');os.chmod(marker,0o600)
    record(marker,'regular',bytes=7,sha256=digest(marker),generated='Cargo registry completion metadata v1; not a checksum claim')
    actual=set()
    for root,ds,fs in os.walk(src,followlinks=False):
     for d in ds:
      q=P(root)/d;assert not q.is_symlink();directories.add(q)
     for f in fs:
      q=P(root)/f;assert stat.S_ISREG(q.lstat().st_mode) and q.stat().st_nlink==1;actual.add(str(q.relative_to(src)))
    assert actual==expected|{'.cargo-ok'}
    for d in sorted(directories):record(d,'directory')
    result.append(dict(crate=crate,index=idx,archive=arc,source_files=len(expected),source_bytes=member_bytes,exact_set=True))
  # Small availability observation only: never invokes these executables.
  tools={}
  for name in ('bwrap','unshare','chroot','strace'):
   p=shutil.which(name,path='/usr/bin:/bin:/usr/sbin:/sbin')
   tools[name]=None if p is None else dict(path=p,resolved=str(P(p).resolve()),sha256=digest(P(p)))
  runtime={}
  runtime_paths={str(P(sys.executable).resolve())}
  for m in list(sys.modules.values()):
   p=getattr(m,'__file__',None)
   if p and P(p).is_file():runtime_paths.add(str(P(p).resolve()))
  for line in P('/proc/self/maps').read_text().splitlines():
   chunks=line.split();p=chunks[-1]
   if p.startswith('/') and P(p).is_file():runtime_paths.add(str(P(p).resolve()))
  for p in sorted(runtime_paths):runtime[p]=dict(bytes=P(p).stat().st_size,sha256=digest(P(p)))
  output=dict(packages=result,files=files,bytes=total,manifest=dict(path=str(manifest),bytes=manifest.stat().st_size,sha256=digest(manifest)),tools=tools,runtime=runtime,empty_targets=['target-verifier','target-pool'],cargo_index='NOT PREPARED; offline resolution closure remains open',source_view='existing frozen own src; equality reused, bind plan pending',limitations='No build, no compiler/runtime correctness, no TOU exclusion, no historical provenance. Source/archive modes preserved; future umask077 is explicit.')
  with (OUT/'preparation.json').open('x') as f:json.dump(output,f,sort_keys=True);f.write('\n')
  receipt.update(exit=0,output=dict(path=str(OUT/'preparation.json'),bytes=(OUT/'preparation.json').stat().st_size,sha256=digest(OUT/'preparation.json')),packages=len(result),files=files,bytes=total,manifest=output['manifest'],tools=tools)
 except Exception as e:
  receipt.update(exit=1,error=repr(e),traceback=traceback.format_exc(),partial_retained=True)
 u=resource.getrusage(0);receipt.update(wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap)
 print(json.dumps(receipt,sort_keys=True));return receipt['exit']
if __name__=='__main__':sys.exit(main())
