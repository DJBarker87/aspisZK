#!/usr/bin/env python3
"""Appended to literal REQUEST by controller. No root access/writes/build."""
import base64,hashlib,json,os,resource,stat,time,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(448*1024**2,448*1024**2))
start=time.monotonic()
def emit(x):print(json.dumps(x,sort_keys=True),flush=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def inspect(p,kind):
    chain=[]
    for a in [*reversed(p.parents),p]:
        s=a.lstat();assert not stat.S_ISLNK(s.st_mode),str(a)
        assert stat.S_ISDIR(s.st_mode) or (a==p and kind=='file' and stat.S_ISREG(s.st_mode)),str(a)
        if str(a).startswith('/home/dombarker'):assert s.st_uid==os.getuid(),str(a)
        chain.append(dict(path=str(a),uid=s.st_uid,gid=s.st_gid,mode=oct(stat.S_IMODE(s.st_mode)),inode=s.st_ino,device=s.st_dev))
    assert str(p.resolve())==str(p)
    return chain
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
count=0
for i,r in enumerate(REQUEST['roots']):
    root=Path(r)
    try:chain=inspect(root,'directory')
    except FileNotFoundError:
        emit(dict(kind='missing-root',root_index=i,path=r));continue
    emit(dict(kind='root-path',root_index=i,path=r,ancestors=chain))
    for m in REQUEST['modules']:
        rel=m.replace('.','/')+'.olean';main=root/rel
        try:main.lstat()
        except FileNotFoundError:continue
        for suffix in ('','.server','.private'):
            p=Path(str(main)+suffix)
            if str(p) in REQUEST.get('already_retained',[]):
                emit(dict(kind='reused-own-capture',path=str(p),root_index=i,module=m,suffix=suffix));continue
            try:p.lstat()
            except FileNotFoundError:
                emit(dict(kind='absent-part',root_index=i,module=m,suffix=suffix));continue
            if stat.S_ISLNK(p.lstat().st_mode):
                emit(dict(kind='excluded-symlink',root_index=i,module=m,path=str(p),assessment='Not followed; this origin is unresolved unless a separately admitted regular origin provides it'));continue
            chain=inspect(p,'file');before=p.stat();assert before.st_size<=64*1024**2
            historical=REQUEST['historical'].get(m+'.olean') if not suffix else None
            if historical and historical['path']!=str(p):historical=None
            pre=digest(p)
            if historical:assert pre==historical['sha256'] and before.st_size==historical['bytes'],str(p)
            with p.open('rb') as f:data=f.read(64*1024**2+1)
            assert len(data)<=64*1024**2
            copied=sha(data);post=digest(p);after=p.stat()
            assert pre==copied==post and (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns)
            emit(dict(kind='part',root_index=i,module=m,suffix=suffix,path=str(p),relative_path=rel+suffix,
                sha256=pre,post_sha256=post,bytes=len(data),source_inode=before.st_ino,source_device=before.st_dev,
                source_mtime_ns=before.st_mtime_ns,source_ctime_ns=before.st_ctime_ns,ancestors=chain,
                historical_assessment='MATCH direct historical main-object receipt' if historical else 'NEW current data observation only; no historical part pin',base64=base64.b64encode(data).decode()))
            del data
            count+=1
            if count==10:
                obs=subprocess.run(['sudo','-n','python3','-'],input=REQUEST['observer'].encode(),capture_output=True,timeout=55)
                assert obs.returncode==0,obs.stderr
                observation=json.loads(obs.stdout)
                emit(dict(kind='during-observation',observation=observation))
                assert observation['allowed_to_enter'],'During-copy metadata admission denied'
u=resource.getrusage(0)
emit(dict(kind='remote-receipt',wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: read-only data copy'))
