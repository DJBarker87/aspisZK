#!/usr/bin/env python3
"""Ordinary-owner donor inventory only. No donor writes or symlink following."""
import hashlib,json,os,pathlib,re,resource,stat,sys,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));start=time.monotonic();P=pathlib.Path
BASE=P('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023');STAGE=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024');OUT=STAGE/'SbfCachePrep-20261024'
assert os.geteuid()==1000
for p in [STAGE,BASE]:
    for q in (p,*p.parents):assert not q.is_symlink()
assert STAGE.stat().st_uid==1000 and stat.S_IMODE(STAGE.stat().st_mode)==0o700
assert (STAGE/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
# Exact already-established identity pins; subset join, not full source replay.
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(1024**2):h.update(b)
    return h.hexdigest()
assert digest(STAGE/'src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert digest(STAGE/'rustc-diagnostics.py')=='fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'
assert not os.path.lexists(OUT);OUT.mkdir(mode=0o700)
rows=[];excluded=[];fingerprints=[];deps=[];total=0
for name in ['sbf-target-verifier','sbf-target-pool']:
    root=BASE/name;assert root.stat().st_uid==1000 and not root.is_symlink()
    pending=[]
    for parent,ds,fs in os.walk(root,followlinks=False):
        for n in sorted(ds+fs):
            p=P(parent)/n;rel=str(p.relative_to(BASE));s=p.lstat()
            row=dict(path=rel,uid=s.st_uid,gid=s.st_gid,mode=oct(stat.S_IMODE(s.st_mode)),bytes=s.st_size,nlink=s.st_nlink,device=s.st_dev,inode=s.st_ino,mtime_ns=s.st_mtime_ns)
            if stat.S_ISLNK(s.st_mode):
                row.update(type='symlink',link=os.readlink(p));raise ValueError('symlink requires separate containment review: '+rel)
            elif stat.S_ISDIR(s.st_mode):row['type']='directory'
            elif stat.S_ISREG(s.st_mode):
                row['type']='regular';total+=s.st_size
                # Metadata names under .fingerprint are Cargo source-package
                # identities, not wallet files. Actual program keypair output
                # and private-key/seed/credential names are excluded first.
                suspicious=re.search(r'(keypair|private.?key|mnemonic|credential|secret|\.pem$|\.key$|\.env(?:\.|$)|id_rsa)',n,re.I)
                is_metadata='.fingerprint' in p.parts and p.suffix in ('.json','.d')
                compiled=p.suffix in ('.rlib','.rmeta','.d','.o','.so','.bc')
                if suspicious and not (is_metadata or compiled):
                    row['excluded']='name-only possible key/secret; not read';excluded.append(rel)
                else:pending.append((p,row))
            else:raise ValueError('special file: '+rel)
            rows.append(row)
    # Complete name/type classification precedes content reads for this root.
    for p,row in pending:
        before=p.lstat();assert stat.S_ISREG(before.st_mode)
        fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
        try:
            s=os.fstat(fd);assert (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns)==(row['device'],row['inode'],row['bytes'],row['mtime_ns'])
            h=hashlib.sha256()
            while b:=os.read(fd,1024**2):h.update(b)
            after=os.fstat(fd);assert (s.st_size,s.st_mtime_ns,s.st_ctime_ns)==(after.st_size,after.st_mtime_ns,after.st_ctime_ns)
            row['sha256']=h.hexdigest()
        finally:os.close(fd)
        if '.fingerprint' in p.parts and p.suffix=='.json':
            assert p.stat().st_size<=2*1024**2
            x=json.loads(p.read_text());fingerprints.append(dict(path=row['path'],sha256=row['sha256'],fields={k:x[k] for k in ('rustc','features','declared_features','target','profile','path','deps','rustflags','config','compile_kind') if k in x},local_kinds=[list(v.keys()) for v in x.get('local',[])]))
        if p.suffix=='.d' and p.stat().st_size<2*1024**2:
            text=p.read_text(errors='replace')
            # Paths only, never dump build-script output/env contents.
            roots=sorted(set(re.findall(r'/home/dombarker/[^\s:]+',text)))
            deps.append(dict(path=row['path'],sha256=row['sha256'],absolute_roots=sorted(set('/'.join(v.split('/')[:6]) for v in roots)),old_source_refs=sum('/codex-cx-s10-repin3-20261023/src/' in v for v in roots),new_source_refs=sum('/codex-cx-sbf-recapture-20261024/src/' in v for v in roots)))
raw=OUT/'inventory.json'
with raw.open('x') as f:json.dump(rows,f,sort_keys=True);f.write('\n')
summary=OUT/'provenance.json'
with summary.open('x') as f:json.dump(dict(fingerprints=fingerprints,dep_info=deps),f,sort_keys=True);f.write('\n')
u=resource.getrusage(0)
print(json.dumps(dict(entries=len(rows),regular_files=sum(x['type']=='regular' for x in rows),total_file_bytes=total,excluded=excluded,fingerprints=len(fingerprints),dep_info=len(deps),old_source_dep_info=sum(x['old_source_refs']>0 for x in deps),new_source_dep_info=sum(x['new_source_refs']>0 for x in deps),outputs=[dict(path=str(p),bytes=p.stat().st_size,sha256=digest(p)) for p in (raw,summary)],copied=False,space_available=os.statvfs(OUT).f_bavail*os.statvfs(OUT).f_frsize,limitation='Inventory is sequential current observation, no atomic snapshot, export, provenance equivalence or TOU claim',receipt=dict(command=[sys.executable,'-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A')),sort_keys=True))
