"""Bounded public source/SDK completion inventory; no executable under review runs."""
import hashlib,json,os,pathlib,re,resource,stat,sys,time,traceback
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077)
P=pathlib.Path;S=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024');B=S/'SbfClosure-20261025-v1';OUT=B/'public-finish-v1.json';start=time.monotonic()
r=dict(command=['python3','-B','-c','literal SbfClosure_public_finish.py via SSH'],print_axioms='N/A')
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return dict(bytes=p.stat().st_size,sha256=h.hexdigest(),mode=stat.S_IMODE(p.stat().st_mode))
try:
 assert B.resolve()==B and B.stat().st_uid==1000 and stat.S_IMODE(B.stat().st_mode)==0o700
 assert (B/'OWNER').read_text()=='SbfClosure 20261025\n'
 assert pin(S/'src/Cargo.lock')['sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 reg=S/'SbfInputs-20261024-v3';assert (reg/'OWNER').read_text()=='SbfInputs 20261024\n'
 mf=reg/'registry-files.jsonl';assert pin(mf)['sha256']=='363a30ed6b0ae67541af8ef7d5ed1ec76888bb8966e64375211e48c95e6503a1'
 rows=[json.loads(s) for s in mf.read_text().splitlines()];known={x['path']:x for x in rows};scripts=[];manifests=[];native=[]
 for name,row in known.items():
  if row['type']!='regular' or not (name.endswith('/build.rs') or name.endswith('/Cargo.toml')):continue
  p=reg/name;assert p.resolve()==p and pin(p)['sha256']==row['sha256'] and p.stat().st_size<1_000_000
  s=p.read_text();item=dict(path=name,**pin(p))
  if name.endswith('/build.rs'):
   # Full script retained; helpers invoked by mod/include!/build path are separately
   # listed as lexical operations, NOT assumed covered by this default-name scan.
   item['text']=s;scripts.append(item)
  else:
   item['build_directives']=[x for x in s.splitlines() if re.search(r'^build\s*=|^links\s*=|\[build-dependencies|^\[package\]',x)];manifests.append(item)
 r['registry_scripts']=scripts;r['registry_manifests']=manifests
 sdk=P('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/sdk/sbf')
 sdkrows=[];sdktexts=[]
 if sdk.is_dir():
  for root,ds,fs in os.walk(sdk,followlinks=False):
   assert len(sdkrows)<10000
   for n in sorted(ds+fs):
    p=P(root)/n;x=dict(path=str(p),mode=stat.S_IMODE(p.lstat().st_mode))
    if p.is_symlink():x.update(type='symlink',link=os.readlink(p),resolved=str(p.resolve()))
    elif p.is_dir():x.update(type='directory')
    elif p.is_file():
     x.update(type='regular',**pin(p))
     if p.suffix in ('.sh','.py') and p.stat().st_size<100000:
      sdktexts.append(dict(path=str(p),text=p.read_text(),**pin(p)))
    else:raise ValueError('special SDK input')
    sdkrows.append(x)
 else:r['sdk_missing']=str(sdk)
 # Earlier package filter intentionally omitted libexec. Record the concrete gap
 # now without running gcc -print* or any compiler, including all native helpers.
 libexec=P('/usr/libexec/gcc/x86_64-linux-gnu/13')
 if libexec.is_dir():
  for root,ds,fs in os.walk(libexec,followlinks=False):
   for n in fs:
    p=P(root)/n
    if p.is_symlink():native.append(dict(path=str(p),type='symlink',link=os.readlink(p),resolved=str(p.resolve())))
    elif p.is_file():native.append(dict(path=str(p),type='regular',**pin(p)))
 r.update(sdk_files=sdkrows,sdk_scripts=sdktexts,native_libexec=native,exit=0,
  limitations='Static public candidate inventory only; SDK symlink targets not copied. Registry default build.rs and normalized Cargo.toml scanned, nonstandard script/helper module closure still requires follow-up. No complete offline resolver/loader/dlopen/execution claim.')
except Exception as e:r.update(exit=1,error=repr(e),traceback=traceback.format_exc())
u=resource.getrusage(0);r.update(wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap)
b=(json.dumps(r,sort_keys=True)+'\n').encode();assert len(b)<5_000_000
with OUT.open('xb') as f:f.write(b)
print(b.decode());sys.exit(r['exit'])
