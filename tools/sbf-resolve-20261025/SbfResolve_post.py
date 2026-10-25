"""Final read-only post seals, not another Cargo invocation or build admission."""
import hashlib,json,os,pathlib,resource,stat,sys,time
P=pathlib.Path
def seal(p):
 for q in [p,*p.parents]:assert not q.is_symlink()
 s=p.stat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return dict(path=str(p),bytes=s.st_size,sha256=h.hexdigest(),mode=stat.S_IMODE(s.st_mode),uid=s.st_uid)
def main():
 req=json.loads(sys.stdin.readline());t=time.monotonic();rows={}
 O=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfResolve-20261025-v1');assert O.stat().st_uid==os.getuid()==1000 and stat.S_IMODE(O.stat().st_mode)==0o700
 for name,expected in req['expected'].items():
  p=P(name);assert p.is_absolute();row=seal(p);assert row==expected;rows[name]=row
 u=resource.getrusage(0);print(json.dumps(dict(exit=0,command=req['command'],source_revision=req['revision'],helper_sha256=req['helper_sha256'],unchanged_post_seals=rows,wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A',limitation='post seals after both queries, no immutable TOU guarantee; only named files, not complete source/runtime/caches')))
if __name__=='__main__':main()
