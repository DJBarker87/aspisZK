"""Future metadata discovery: fixed finite roots, no symlink traversal or tools."""
import os
import stat
import time
from pathlib import PurePosixPath
from FinalNativeGate_bounded import Reader, CatalogError, stamp


def discover(roots,entry_limit,deadline):
    rows={};missing=[];seen=set()
    def tick():
        if time.monotonic()>deadline:raise CatalogError('discovery deadline')
    def row(path,s):
        tick()
        if path not in rows and len(rows)>=entry_limit:raise CatalogError('historical entry envelope exhausted; new collection proposal required')
        kind='dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'link' if stat.S_ISLNK(s.st_mode) else 'unknown'
        e=dict(kind=kind,uid=s.st_uid,gid=s.st_gid,mode=s.st_mode)
        if kind=='file':e['size']=s.st_size
        if kind in ('link','unknown') or s.st_mode&0o022:
            missing.append(dict(path=path,reason='alias requires explicit complete chain review' if kind=='link' else 'type/permissions require review'))
        if path in rows and any(rows[path][k]!=v for k,v in e.items()):raise CatalogError('discovery metadata drift')
        rows.setdefault(path,e);return rows[path]
    def visit(fd,path,recurse):
        tick();s=os.fstat(fd);e=row(path,s)
        if e['kind']!='dir' or not recurse:return
        identity=(s.st_dev,s.st_ino)
        if identity in seen:raise CatalogError('directory cycle/duplicate inventory root')
        seen.add(identity);names=[]
        with os.scandir(fd) as entries:
            for entry in entries:
                tick();names.append(entry.name)
                if len(names)+len(rows)>entry_limit:raise CatalogError('directory envelope exhausted')
        e['children']=sorted(names)
        for name in sorted(names):
            target=path.rstrip('/')+'/'+name
            before=os.stat(name,dir_fd=fd,follow_symlinks=False);child=row(target,before)
            if child['kind']=='link':
                child['target']=os.readlink(name,dir_fd=fd)
            elif child['kind'] in ('dir','file'):
                sub=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|(os.O_DIRECTORY if child['kind']=='dir' else 0),dir_fd=fd)
                try:
                    if stamp(os.fstat(sub))!=stamp(before):raise CatalogError('discovery open race')
                    visit(sub,target,True)
                finally:os.close(sub)
            if stamp(os.stat(name,dir_fd=fd,follow_symlinks=False))!=stamp(before):raise CatalogError('discovery child drift')
        if stamp(os.fstat(fd))!=stamp(s):raise CatalogError('discovery directory drift')
    for root in roots:
        parts=PurePosixPath(root).parts
        if not root.startswith('/') or str(PurePosixPath(root))!=root or '..' in parts:raise CatalogError('noncanonical fixed root')
        fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        try:
            row('/',os.fstat(fd));current=''
            for i,name in enumerate(parts[1:]):
                current+='/'+name
                try:s=os.stat(name,dir_fd=fd,follow_symlinks=False)
                except FileNotFoundError:
                    missing.append(dict(path=current,reason='missing fixed input'));break
                e=row(current,s)
                if e['kind']=='link':
                    e['target']=os.readlink(name,dir_fd=fd);break
                if e['kind']=='unknown':break
                sub=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|(os.O_DIRECTORY if e['kind']=='dir' else 0),dir_fd=fd)
                if stamp(os.fstat(sub))!=stamp(s):os.close(sub);raise CatalogError('root open race')
                os.close(fd);fd=sub
                if i==len(parts)-2:visit(fd,current,True)
        finally:os.close(fd)
    # Exact observed sizes become candidate bounds, never activation pins.
    total=sum(e.get('size',0) for e in rows.values())
    catalog=dict(entries=rows,roots=roots,bounds=dict(files=entry_limit,bytes=max(1,total),seconds=115),
        rationale='entry ceiling is historical MIR count50077 plus fixed source/root count; no increase on failure; bytes are sum of exact stat sizes;115s allocation deadline')
    return catalog,missing
