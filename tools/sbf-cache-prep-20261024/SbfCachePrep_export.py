#!/usr/bin/env python3
"""Copy verified named donors privately; no donor writes or hardlinks."""
import hashlib,json,os,pathlib,resource,stat,sys,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));start=time.monotonic();P=pathlib.Path
BASE=P('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023');STAGE=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024');OUT=STAGE/'SbfCachePrep-20261024';DEST=OUT/'snapshot'
assert os.getuid()==1000
for p in (STAGE,OUT,BASE):
    for q in (p,*p.parents):assert not q.is_symlink()
assert STAGE.stat().st_uid==1000 and stat.S_IMODE(STAGE.stat().st_mode)==0o700
assert (STAGE/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
def digest(p):
    h=hashlib.sha256()
    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
    try:
        assert stat.S_ISREG(os.fstat(fd).st_mode)
        while b:=os.read(fd,1024**2):h.update(b)
    finally:os.close(fd)
    return h.hexdigest()
raw=OUT/'inventory.json';assert digest(raw)=='e98de11bf81d5497652882f2663c6eedec3a0aa13a3ae14877f79da946b07541';rows=json.loads(raw.read_text())
assert digest(STAGE/'src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert digest(STAGE/'rustc-diagnostics.py')=='fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'
assert not any(r.get('excluded') for r in rows) and all(r['type'] in ('directory','regular') for r in rows)
total=sum(r['bytes'] for r in rows if r['type']=='regular');free=os.statvfs(OUT).f_bavail*os.statvfs(OUT).f_frsize
assert free>total+1024**3,'insufficient exact copy size plus1GiB reserve'
expected={r['path']:r for r in rows}
def names():
    result=set()
    for name in ('sbf-target-verifier','sbf-target-pool'):
        root=BASE/name;assert not root.is_symlink() and root.stat().st_uid==1000
        for parent,ds,fs in os.walk(root,followlinks=False):
            for n in ds+fs:
                p=P(parent)/n;assert not p.is_symlink();result.add(str(p.relative_to(BASE)))
    return result
assert names()==set(expected),'donor set changed before copy'
# Full pre-hash all files before creating any snapshot. Existing exclusions
# were classified before acquisition; reject every new name before reading.
for r in rows:
    p=BASE/r['path'];s=p.lstat();assert s.st_uid==r['uid'] and stat.S_IMODE(s.st_mode)==int(r['mode'],8)
    if r['type']=='regular':assert stat.S_ISREG(s.st_mode) and s.st_size==r['bytes'] and digest(p)==r['sha256']
    else:assert stat.S_ISDIR(s.st_mode)
assert not os.path.lexists(DEST);DEST.mkdir(mode=0o700)
for name in ('sbf-target-verifier','sbf-target-pool'):(DEST/name).mkdir(mode=0o700)
for r in sorted(rows,key=lambda r:(len(P(r['path']).parts),r['path'])):
    src=BASE/r['path'];dest=DEST/r['path']
    if r['type']=='directory':dest.mkdir(mode=int(r['mode'],8));continue
    fd=os.open(src,os.O_RDONLY|os.O_NOFOLLOW);out=os.open(dest,os.O_WRONLY|os.O_CREAT|os.O_EXCL,int(r['mode'],8))
    try:
        s=os.fstat(fd);d=os.fstat(out);assert stat.S_ISREG(s.st_mode) and (s.st_dev,s.st_ino)!=(d.st_dev,d.st_ino) and d.st_nlink==1
        before=(s.st_size,s.st_mtime_ns,s.st_ctime_ns);h=hashlib.sha256();count=0
        while b:=os.read(fd,1024**2):
            h.update(b);count+=len(b);view=memoryview(b)
            while view:view=view[os.write(out,view):]
        assert count==r['bytes'] and h.hexdigest()==r['sha256'];s=os.fstat(fd);assert before==(s.st_size,s.st_mtime_ns,s.st_ctime_ns)
    finally:os.close(fd);os.close(out)
# Complete source and private destination post-content hashes and file-set check.
assert names()==set(expected),'donor set changed after copy'
private=[]
for r in rows:
    src=BASE/r['path'];dest=DEST/r['path'];s=src.lstat();d=dest.lstat()
    assert not src.is_symlink() and not dest.is_symlink()
    assert stat.S_IMODE(s.st_mode)==int(r['mode'],8)
    if r['type']=='regular':
        assert stat.S_ISREG(s.st_mode) and stat.S_ISREG(d.st_mode) and s.st_size==d.st_size==r['bytes']
        assert digest(src)==digest(dest)==r['sha256'];assert (s.st_dev,s.st_ino)!=(d.st_dev,d.st_ino) and d.st_nlink==1
        private.append(dict(path=r['path'],sha256=r['sha256'],bytes=r['bytes'],source_device=s.st_dev,source_inode=s.st_ino,destination_device=d.st_dev,destination_inode=d.st_ino,destination_nlink=d.st_nlink,mode=oct(stat.S_IMODE(d.st_mode))))
post=OUT/'snapshot-manifest.json'
with post.open('x') as f:json.dump(private,f,sort_keys=True);f.write('\n')
u=resource.getrusage(0)
print(json.dumps(dict(copied=True,files=len(private),bytes=total,space_before=free,space_after=os.statvfs(OUT).f_bavail*os.statvfs(OUT).f_frsize,method='exclusive private regular streaming copies; no donor hardlinks',source_pre_copy_post_equal=True,output=dict(path=str(post),bytes=post.stat().st_size,sha256=digest(post)),limitation='Sequential complete hashes, not an atomic snapshot or exclusion of future writes; post process observation still required. No execution/readiness claim.',receipt=dict(command=[sys.executable,'-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A')),sort_keys=True))
