#!/usr/bin/env python3
"""Bounded public index preparation and one Python-only unprivileged namespace probe."""
import hashlib,json,os,pathlib,resource,stat,subprocess,sys,time,traceback
P=pathlib.Path;S=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024');O=S/'SbfInputs-20261024-v3'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def check(p):
 for q in (p,*p.parents):assert not q.is_symlink()
 assert stat.S_ISREG(p.stat().st_mode)
def index_rel(name):
 assert name and all(c in 'abcdefghijklmnopqrstuvwxyz0123456789_-' for c in name)
 return ('1/'+name if len(name)==1 else '2/'+name if len(name)==2 else '3/'+name[0]+'/'+name if len(name)==3 else name[:2]+'/'+name[2:4]+'/'+name)
def probe_command():
 child='import os,resource,json;resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));assert os.getuid()!=0;print(json.dumps({"guest_pid":os.getpid(),"uid":os.getuid(),"status":"namespace creation only; no filesystem isolation claim"}))'
 return ['/usr/bin/unshare','--user','--map-current-user','--mount','--net','--pid','--fork','--','/usr/bin/python3','-I','-S','-B','-c',child]
def main():
 resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077);start=time.monotonic();result={}
 try:
  req=json.loads(sys.stdin.readline());result.update(source_revision=req['revision'],helper_sha256=req['helper_sha256'])
  assert O.resolve()==O and O.stat().st_uid==os.getuid()==1000 and stat.S_IMODE(O.stat().st_mode)==0o700
  assert (O/'OWNER').read_text()=='SbfInputs 20261024\n'
  check(O/'preparation.json');assert sha(O/'preparation.json')==req['preparation_sha256']
  packages=json.loads((O/'preparation.json').read_text())['packages'];rows=[];seen=set()
  for pkg in packages:
   crate=pkg['crate'];name,version=crate.rsplit('-',1);idx=pkg['index'];rel=index_rel(name)
   src=P('/home/dombarker/.cargo/registry/index')/idx/'.cache'/rel;check(src);assert src.stat().st_size<16*1024**2
   b=src.read_bytes();assert len(b)>5 and b[0]==3
   entries=[]
   for part in b[5:].split(b'\0'):
    if part.startswith(b'{'):
     x=json.loads(part)
     if x.get('vers')==version:entries.append(x)
   assert len(entries)==1 and entries[0]['name']==name and entries[0]['cksum']==pkg['archive']['sha256']
   dst=O/'cargo/registry/index'/idx/'.cache'/rel
   if str(dst) not in seen:
    dst.parent.mkdir(parents=True,exist_ok=True)
    with dst.open('xb') as f:f.write(b)
    os.chmod(dst,stat.S_IMODE(src.stat().st_mode));assert sha(dst)==hashlib.sha256(b).hexdigest();seen.add(str(dst))
   rows.append(dict(crate=crate,path=str(dst.relative_to(O)),bytes=len(b),sha256=sha(dst),locked_entry_checksum=entries[0]['cksum']))
  # This is public registry endpoint configuration, never Cargo user config/credentials.
  idx=packages[0]['index'];src=P('/home/dombarker/.cargo/registry/index')/idx/'config.json';check(src);assert src.stat().st_size<4096
  b=src.read_bytes();cfg=json.loads(b);assert set(cfg)<={'dl','api','auth-required'} and cfg.get('auth-required',False)==False
  assert cfg['dl']=='https://static.crates.io/crates' and cfg.get('api')=='https://crates.io'
  dst=O/'cargo/registry/index'/idx/'config.json'
  with dst.open('xb') as f:f.write(b)
  os.chmod(dst,stat.S_IMODE(src.stat().st_mode))
  result.update(index_rows=rows,index_files=len(seen),public_config=dict(path=str(dst),bytes=len(b),sha256=sha(dst)))
  expected='a23c8863860669003dc4660039fe642f5795c8c2195898ebc5d01afa1ac3d11c';assert sha(P('/usr/bin/unshare'))==expected
  cmd=probe_command();t=time.monotonic();p=subprocess.run(cmd,capture_output=True,timeout=10,env={'PATH':'/usr/bin:/bin','LC_ALL':'C'})
  assert len(p.stdout)<4096 and len(p.stderr)<4096
  result['namespace_probe']=dict(command=cmd,exit=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),wall_seconds=time.monotonic()-t,unshare_sha256=expected,assessment='creation only; mounts not tested; failure blocks unprivileged plan, no privilege escalation')
  result['exit']=0
 except Exception as e:result.update(exit=1,error=repr(e),traceback=traceback.format_exc(),partial_retained=True)
 u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN);result.update(command=req['host_command'],wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,children_peak_rss_kib=c.ru_maxrss,swap=u.ru_nswap+c.ru_nswap,print_axioms='N/A')
 with (O/'finish.json').open('x') as f:json.dump(result,f,sort_keys=True);f.write('\n')
 print(json.dumps(result,sort_keys=True));return result['exit']
if __name__=='__main__':sys.exit(main())
