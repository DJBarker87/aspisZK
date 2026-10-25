"""Public data prep and at most two metadata observations. Never build/scope/privilege."""
import hashlib,json,os,pathlib,resource,signal,stat,subprocess,sys,time,tomllib,traceback,threading,tarfile,re,urllib.request
P=pathlib.Path
S=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024'); O=S/'SbfResolve-20261025-v1'; OLD=S/'SbfInputs-20261024-v3'
IDX='index.crates.io-1949cf8c6b5b557f'; PLATFORM=P('/home/dombarker/.cache/solana/v1.52/platform-tools'); LIMIT=512*1024**2
PINS={'source-inputs.json':'a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1','src/Cargo.lock':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','rustc-diagnostics.py':'fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'}
R={}; peak=0;swappeak=0;stop=threading.Event();violation=threading.Event()
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def no_links(p):
 for q in (p,*p.parents):assert not q.is_symlink(),str(q)
def seal(p):
 no_links(p);s=p.stat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
 return dict(path=str(p),bytes=s.st_size,sha256=digest(p),mode=stat.S_IMODE(s.st_mode),uid=s.st_uid)
def copy(src,dst,sha=None):
 a=seal(src);assert a['bytes']<=32*1024**2 or src.is_relative_to(OLD)
 if sha:assert a['sha256']==sha
 dst.parent.mkdir(mode=0o700,parents=True,exist_ok=True)
 with src.open('rb') as f,dst.open('xb') as g:
  while b:=f.read(1024**2):g.write(b)
 os.chmod(dst,a['mode']);b=seal(dst);assert b['sha256']==a['sha256'] and src.stat().st_ino!=dst.stat().st_ino and seal(src)==a
 return b
def admission():
 rows=[];root=P('/sys/fs/cgroup')
 def walk(p):
  if p!=root and dict(x.split() for x in (p/'cgroup.events').read_text().splitlines()).get('populated')!='1':return
  cap=(p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
  if cap!='max':rows.append(dict(path=str(p),memory_max=int(cap)));return
  for q in p.iterdir():
   if q.is_dir():walk(q)
 walk(root);total=sum(x['memory_max'] for x in rows)
 mem=dict((a,int(b.split()[0])*1024) for a,b in (l.split(':',1) for l in P('/proc/meminfo').read_text().splitlines()))
 result=dict(reservations=rows,sum_memory_max=total,mem_available=mem['MemAvailable'],kind='bounded metadata/data preparation only; not build GO')
 assert total+LIMIT<55*1024**3 and mem['MemAvailable']>=7*1024**3+LIMIT,result
 return result
def resident():
 global peak,swappeak
 # Inspect only self and descendants, no unrelated cmdline/environ/FD buffers.
 pairs={}
 for p in P('/proc').iterdir():
  if p.name.isdigit():
   try:s=p.joinpath('stat').read_text().rsplit(')',1)[1].split();pairs[int(p.name)]=int(s[1])
   except (FileNotFoundError,ProcessLookupError,PermissionError):pass
 ids={os.getpid()}
 while True:
  more={pid for pid,ppid in pairs.items() if ppid in ids};new=ids|more
  if new==ids:break
  ids=new
 rss=swap=0
 for pid in ids:
  try:
   d=dict(l.split(':',1) for l in P(f'/proc/{pid}/status').read_text().splitlines() if ':' in l)
   rss+=int(d.get('VmRSS','0 kB').split()[0])*1024;swap+=int(d.get('VmSwap','0 kB').split()[0])*1024
  except (FileNotFoundError,ProcessLookupError):pass
 peak=max(peak,rss);swappeak=max(swappeak,swap)
 return rss,ids
def monitor():
 while not stop.wait(.02):
  rss,ids=resident()
  if rss>=LIMIT:
   violation.set()
   for pid in ids-{os.getpid()}:
    try:os.kill(pid,signal.SIGKILL)
    except ProcessLookupError:pass
   return

def tools():
 return {str(p):seal(p) for p in [PLATFORM/'rust/bin/cargo',PLATFORM/'rust/bin/rustc',P('/usr/bin/strace'),P('/usr/bin/python3.12')]}
def verify_parent():
 no_links(S);assert S.stat().st_uid==os.getuid()==1000 and stat.S_IMODE(S.stat().st_mode)==0o700
 assert (S/'OWNER').read_bytes()==b'SbfRecapturePrep 20261024\n'
 for p,h in PINS.items():assert digest(S/p)==h
 return {p:seal(S/p) for p in PINS}
def init(req):
 R['parent_pins']=verify_parent();R['admission']=admission();R['tools_before']=tools()
 for p,h in req['tool_pins'].items():assert R['tools_before'][p]['sha256']==h
 O.mkdir(mode=0o700);(O/'OWNER').write_text('SbfResolve 20261025\n')
 for d in ['home','cargo','rustup','tmp','target']:(O/d).mkdir(mode=0o700)
 cwd=P('/tmp/SbfResolve-20261025-v1');cwd.mkdir(mode=0o700);R['cwd']=str(cwd)
 absence=[]
 for d in [cwd,*cwd.parents]:
  for name in ['config','config.toml']:
   p=d/'.cargo'/name;assert not p.exists() and not p.is_symlink(),str(p);absence.append(str(p))
 R['config_absent']=absence
 for name,body in req['helpers'].items():
  assert name in ['SbfResolve_guard.py','SbfResolve_host.py']
  (O/name).write_text(body);os.chmod(O/name,0o700 if name.endswith('guard.py') else 0o600)
 config=b'[net]\noffline = true\n';(O/'cargo/config.toml').write_bytes(config)
 # Exact reviewed123 public archive-derived view; no old global unpacked trees.
 assert digest(OLD/'registry-files.jsonl')=='363a30ed6b0ae67541af8ef7d5ed1ec76888bb8966e64375211e48c95e6503a1'
 rows=[json.loads(x) for x in (OLD/'registry-files.jsonl').read_text().splitlines()];copied=[]
 for row in rows:
  rel=P(row['path']);assert not rel.is_absolute() and '..' not in rel.parts and rel.parts[0]=='cargo'
  if row['type']=='regular':copied.append(copy(OLD/rel,O/rel,row['sha256']))
  else:assert row['type']=='directory';(O/rel).mkdir(mode=0o700,parents=True,exist_ok=True)
 for rel,row in req['indices'].items():
  assert rel.startswith('cargo/registry/index/'+IDX+'/') and '..' not in P(rel).parts
  copied.append(copy(OLD/rel,O/rel,row['sha256']))
 # Published directory permission bits preserved after descendants copied.
 for row in reversed(rows):
  if row['type']=='directory':os.chmod(O/row['path'],int(row['mode'],8))
 (O/'private-cache-initial.json').write_text(json.dumps(copied,sort_keys=True)+'\n')
 R['cache_initial']=dict(files=len(copied),bytes=sum(r['bytes'] for r in copied),manifest=seal(O/'private-cache-initial.json'))
 R['source_reuse']='7978 files/104193141 bytes at frozen4bb reused; no full replay, manifests freshly pinned'
 manifests={r['path']:r for r in req['manifests']}
 sourcepins={}
 for rel,row in manifests.items():
  assert digest(S/rel)==row['sha256'];sourcepins[rel]=seal(S/rel)
 (O/'source-pins.json').write_text(json.dumps(sourcepins,sort_keys=True)+'\n');R['source_pins']=sourcepins
 control=dict(rustc=str(PLATFORM/'rust/bin/rustc'),rustc_sha256=R['tools_before'][str(PLATFORM/'rust/bin/rustc')]['sha256'],cwd=str(cwd),cargo=str(PLATFORM/'rust/bin/cargo'))
 (O/'control.json').write_text(json.dumps(control)+'\n');R['control']=seal(O/'control.json');R['tools_after']=tools();assert R['tools_after']==R['tools_before']

def index_rel(n):
 assert re.fullmatch('[a-zA-Z0-9_-]+',n);n=n.lower()
 return '1/'+n if len(n)==1 else '2/'+n if len(n)==2 else '3/'+n[0]+'/'+n if len(n)==3 else n[:2]+'/'+n[2:4]+'/'+n

def fixture_allowed(q,checksum):
 public_winapi={'winapi-i686-pc-windows-gnu-0.4.0': 'ac3b87c63620426dd9b991e5ce0329eff545bccbbb34f3be09ff6fb6ab51b7b6', 'winapi-x86_64-pc-windows-gnu-0.4.0': '712e227841d057c1ee1cd2fb22fa7e5a5461ae8e48fa2ca79ec42cfc1931183f'}
 if len(q.parts)==3 and q.parts[0] in public_winapi and public_winapi[q.parts[0]]==checksum and q.parts[1]=='lib' and q.name.startswith('libwinapi_') and q.suffix=='.a':return True
 return (str(q),checksum)==('untrusted-0.9.0/mk/llvm-snapshot.gpg.key','8ecb6da28b8a351d773b68d5825ac39017e680750f980f3a1a85cd8dd28a47c1') or any(x in q.parts[1:-1] for x in ('test','tests','testdata','examples','data','fixtures')) or (str(q),checksum)==('ring-0.17.14/src/rsa/signature_rsa_example_private_key.der','a4689e6c2294d81e88dc6261c768b63bc4fcdb852be6d1352498b114f61383b7')

def universe(req):
 R['parent_pins']=verify_parent();R['admission']=admission()
 lock=tomllib.loads((S/'src/Cargo.lock').read_text());pkgs=[p for p in lock['package'] if p.get('source','').startswith('registry+')];assert len(pkgs)==428
 downloads=0;rows=[];attempts=[];R['attempts']=attempts;R['public_fixture_names']=[]
 for p in pkgs:
  assert p['source']=='registry+https://github.com/rust-lang/crates.io-index'
  name,version=p['name'],p['version'];crate=name+'-'+version;assert re.fullmatch('[a-zA-Z0-9_.+-]+',crate)
  rel=index_rel(name);idxdst=O/'cargo/registry/index'/IDX/'.cache'/rel
  if not idxdst.exists():
   src=P('/home/dombarker/.cargo/registry/index')/IDX/'.cache'/rel
   data=src.read_bytes() if src.exists() and not src.is_symlink() and src.stat().st_size<16*1024**2 else b''
   assert data and data[0]==3,'missing public index '+name
   records=[json.loads(b) for b in data[5:].split(b'\0') if b.startswith(b'{')]
   selected=[r for r in records if r.get('vers')==version and r.get('name')==name]
   assert len(selected)==1 and selected[0]['cksum']==p['checksum'],'index checksum '+crate
   copy(src,idxdst)
  data=idxdst.read_bytes();selected=[json.loads(b) for b in data[5:].split(b'\0') if b.startswith(b'{') and json.loads(b).get('vers')==version]
  assert len(selected)==1 and selected[0]['name']==name and selected[0]['cksum']==p['checksum']
  dest=O/'cargo/registry/cache'/IDX/(crate+'.crate');origin='reused123'
  if not dest.exists():
   src=P('/home/dombarker/.cargo/registry/cache')/IDX/(crate+'.crate')
   if src.exists():copy(src,dest,p['checksum']);origin='public archive cache'
   else:
    url='https://static.crates.io/crates/'+name+'/'+crate+'.crate';a=dict(url=url,status='attempting');attempts.append(a)
    # Flush attempts before transport; same URL never retried.
    (O/'download-attempts.json').write_text(json.dumps(attempts)+'\n')
    t=time.monotonic();dest.parent.mkdir(mode=0o700,parents=True,exist_ok=True);total=0
    with urllib.request.urlopen(url,timeout=25) as response,dest.open('xb') as out:
     a['status']=response.status;a['final_url']=response.url;assert response.url==url
     while b:=response.read(1024**2):
      total+=len(b);downloads+=len(b);assert total<=32*1024**2 and downloads<=256*1024**2
      out.write(b)
    a.update(bytes=total,sha256=digest(dest),wall_seconds=time.monotonic()-t);assert a['sha256']==p['checksum'];origin='exact HTTPS locked archive'
  assert digest(dest)==p['checksum'];root=O/'cargo/registry/src'/IDX/crate
  if not root.exists():
   # Validate entire archive before extraction, retaining failed archives.
   with tarfile.open(dest,'r:gz') as tar:
    members=tar.getmembers();assert len(members)<20000;seen=set();total=0
    for m in members:
     q=pathlib.PurePosixPath(m.name);assert m.name and not q.is_absolute() and '..' not in q.parts and '\\' not in m.name and q.parts[0]==crate and str(q)==m.name.rstrip('/')
     assert str(q) not in seen;seen.add(str(q));assert m.isfile() or m.isdir()
     assert (m.mode & ~0o777) in (0,stat.S_IFREG if m.isfile() else stat.S_IFDIR)
     assert 0<=m.size<=32*1024**2;total+=m.size;assert total<=128*1024**2
     assert q.name not in ('.cargo-ok','.cargo-checksum.json')
     if re.search(r'(keypair|private.?key|mnemonic|credential|secret|\.pem$|\.key$|\.env(?:\.|$)|id_rsa)',q.name,re.I) and q.suffix not in ('.rs','.toml','.md','.txt'):
      assert fixture_allowed(q,p['checksum']),'nonfixture possible key filename '+m.name
      R['public_fixture_names'].append(dict(archive_sha256=p['checksum'],path=m.name,classification='published locked-package test/example, public signing or Windows import-library data, not user/task wallet data'))
    root.mkdir(mode=0o700,parents=True)
    for m in members:
     q=O/'cargo/registry/src'/IDX/m.name
     if m.isdir():q.mkdir(mode=0o700,parents=True,exist_ok=True)
     else:
      q.parent.mkdir(mode=0o700,parents=True,exist_ok=True)
      with tar.extractfile(m) as inp,q.open('xb') as out:
       while b:=inp.read(1024**2):out.write(b)
      assert q.stat().st_size==m.size;os.chmod(q,m.mode&0o777)
    for m in members:
     if m.isdir():os.chmod(O/'cargo/registry/src'/IDX/m.name,m.mode&0o777)
   (root/'.cargo-ok').write_bytes(b'{"v":1}')
  rows.append(dict(name=name,version=version,checksum=p['checksum'],archive=seal(dest),index=seal(idxdst),origin=origin))
  assert not violation.is_set()
 R['locked_universe']=rows;R['download_bytes']=downloads;R['selection']='428 locked public registry entries: conservative metadata superset, not compiled dependency necessity'
 # Finite new private file/mode/hash manifest (may exceed5MB, remote only).
 mf=O/'private-cache-complete.jsonl'
 with mf.open('x') as out:
  for p in sorted((O/'cargo/registry').rglob('*')):
   assert not p.is_symlink()
   if p.is_file():out.write(json.dumps(seal(p),sort_keys=True)+'\n')
 R['private_cache_manifest']=seal(mf)

def query(req):
 q=req['number'];assert q in [1,2]
 R['parent_pins_before']=verify_parent();R['admission']=admission();R['tools_before']=tools()
 R['runtime_before']={p:seal(P(p)) for p in req['runtime_pins']}
 for p,h in req['runtime_pins'].items():assert R['runtime_before'][p]['sha256']==h
 control=json.loads((O/'control.json').read_text());cwd=P(control['cwd']);absence=[]
 for d in [cwd,*cwd.parents]:
  for n in ['config','config.toml']:
   p=d/'.cargo'/n;assert not p.exists() and not p.is_symlink();absence.append(str(p))
 R['config_absent']=absence;R['loaded_config_candidates']=[seal(O/'cargo/config.toml')]
 for n in ['credentials','credentials.toml','config'] :assert not (O/'cargo'/n).exists()
 env={'PATH':'/usr/bin:/bin','LC_ALL':'C','HOME':str(O/'home'),'CARGO_HOME':str(O/'cargo'),'RUSTUP_HOME':str(O/'rustup'),'TMPDIR':str(O/'tmp'),'RUSTUP_AUTO_INSTALL':'0','RUSTUP_NO_UPDATE_CHECK':'1','CARGO_NET_OFFLINE':'true','CARGO_TARGET_DIR':str(O/'target'),'CARGO_CACHE_RUSTC_INFO':'0','RUSTC':control['rustc'],'RUSTC_WRAPPER':str(O/'SbfResolve_guard.py')}
 cmd=[control['cargo'],'metadata','--offline','--locked','--format-version','1']
 if q==1:cmd+=['--no-deps']
 else:cmd+=['--filter-platform','sbpf-solana-solana']
 cmd+=['--manifest-path',str(S/'src/programs/r1-cost-probe/Cargo.toml')]
 # Durable exclusive budget charge before the actual CLI call.
 for n in range(1,q):assert (O/f'query-{n}-charged.json').exists()
 charge=O/f'query-{q}-charged.json'
 with charge.open('x') as f:json.dump(dict(argv=cmd,env=env,source_revision=req['revision']),f)
 stdout=O/f'query-{q}.stdout';stderr=O/f'query-{q}.stderr';trace=O/f'query-{q}.trace'
 traced=['/usr/bin/strace','-f','-qq','-s','4096','-e','trace=%file,%process','-o',str(trace),'--']+cmd
 R.update(command=cmd,trace_command=traced,environment=env,cwd=str(cwd),charge=seal(charge),helper=seal(O/'SbfResolve_host.py'),guard=seal(O/'SbfResolve_guard.py'))
 t=time.monotonic()
 with stdout.open('xb') as out,stderr.open('xb') as err:
  p=subprocess.Popen(traced,stdin=subprocess.DEVNULL,stdout=out,stderr=err,cwd=cwd,env=env,start_new_session=True)
  while p.poll() is None:
   if violation.is_set() or time.monotonic()-t>90 or any(x.exists() and x.stat().st_size>32*1024**2 for x in [stdout,stderr,trace]):
    os.killpg(p.pid,signal.SIGKILL);R['aborted']='RSS/deadline/output bound';break
   time.sleep(.02)
  R['cargo_exit']=p.wait();R['cargo_wall_seconds']=time.monotonic()-t
 R['outputs']={n:seal(path) for n,path in [('stdout',stdout),('stderr',stderr),('trace',trace)]}
 R['stderr']=stderr.read_text()[:10000];R['compiler_queries']=[json.loads(l) for l in (O/'compiler-queries.jsonl').read_text().splitlines()] if (O/'compiler-queries.jsonl').exists() else []
 R['tools_after']=tools();assert R['tools_before']==R['tools_after']
 R['runtime_after']={p:seal(P(p)) for p in req['runtime_pins']};assert R['runtime_before']==R['runtime_after']
 R['source_pins_after']={rel:seal(S/rel) for rel in json.loads((O/'source-pins.json').read_text())};assert R['source_pins_after']==json.loads((O/'source-pins.json').read_text())
 R['parent_pins_after']=verify_parent();assert R['parent_pins_before']==R['parent_pins_after']
 if R['cargo_exit']==0:
  data=json.loads(stdout.read_text());R['metadata_summary']=dict(packages=len(data['packages']),workspace_members=data['workspace_members'],workspace_default_members=data['workspace_default_members'],resolve_null=data['resolve'] is None,resolve_nodes=len(data['resolve']['nodes']) if data['resolve'] else None,registry_packages=[dict(name=p['name'],version=p['version'],id=p['id']) for p in data['packages'] if p['source']],workspace_root=data['workspace_root'],target_directory=data['target_directory'])
 R['scope']='workspace metadata/default features; no compilation; query2 sbpf filter plus host/dev discovery'
 assert not violation.is_set()

def main():
 req=json.loads(sys.stdin.readline());op=req['operation'];t=time.monotonic();os.umask(0o077)
 R.update(operation=op,source_revision=req['revision'],host_command=req['host_command'],helper_sha256=req['helper_sha256'],print_axioms='N/A: metadata/data observations; no theorem',rlimits={n:list(resource.getrlimit(getattr(resource,n))) for n in ['RLIMIT_AS','RLIMIT_DATA','RLIMIT_RSS']})
 th=threading.Thread(target=monitor,daemon=True);th.start()
 try:
  assert op in ['init','universe','query'];globals()[op](req);R['exit']=0
 except Exception as e:R.update(exit=1,error=repr(e),traceback=traceback.format_exc(),failed_data_retained=True)
 finally:
  resident();stop.set();th.join();u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
  R.update(wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,sampled_aggregate_rss_bytes=peak,sampled_aggregate_swap_bytes=swappeak,swap=u.ru_nswap+c.ru_nswap,rss_limit_bytes=LIMIT)
  raw=json.dumps(R,sort_keys=True)+'\n';name=op+('-'+str(req['number']) if op=='query' else '')+'-receipt.json'
  if O.exists():
   with (O/(req.get('receipt_name',name))).open('x') as f:f.write(raw)
  print(raw)
 return R['exit']
if __name__=='__main__':sys.exit(main())
