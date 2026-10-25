"""Finite reviewed catalogs only. No forest discovery, implicit alias or whole read."""
import contextlib
import hashlib
import os
import posixpath
import stat
import time

CHUNK = 64 * 1024  # constant resident hashing buffer, independent of file size

class CatalogError(ValueError):
    pass


def stamp(s):
    return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_size,
            s.st_mtime_ns,s.st_ctime_ns,s.st_nlink)


class Reader:
    def __init__(self, catalog):
        if not catalog or not catalog.get('rationale'):
            raise CatalogError('missing reviewed finite catalog/bound rationale')
        self.catalog=catalog; self.entries=catalog['entries']; self.bounds=catalog['bounds']
        self.deadline=time.monotonic()+self.bounds['seconds']; self.used=0; self.files=0
        if any(type(self.bounds[k]) is not int or self.bounds[k]<=0 for k in ('files','bytes','seconds')):
            raise CatalogError('invalid finite bounds')
        if len(self.entries)>self.bounds['files']:raise CatalogError('entry count bound')
        for path in self.entries:
            if not path.startswith('/') or posixpath.normpath(path)!=path or path.startswith('//'):
                raise CatalogError('noncanonical catalog path')

    def tick(self):
        if time.monotonic()>self.deadline:raise CatalogError('catalog deadline')

    def assess(self,path,s):
        self.tick(); e=self.entries[path]
        kind='dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'link' if stat.S_ISLNK(s.st_mode) else 'unknown'
        if kind!=e['kind'] or any(getattr(s,'st_'+k)!=e[k] for k in ('uid','gid','mode')):
            raise CatalogError('entry type/owner/group/mode drift: '+path)
        if kind!='link' and s.st_mode & 0o022:raise CatalogError('group/world writable input: '+path)
        if kind=='file' and s.st_size!=e['size']:raise CatalogError('planned size drift: '+path)
        if kind=='unknown':raise CatalogError('unknown entry type')

    @contextlib.contextmanager
    def opened(self,path):
        """Every component has metadata; explicit links expand only into catalog."""
        held=[]; links=[]; seen=set(); pending=path; final=None
        try:
            while True:
                self.tick()
                fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
                held.append((fd,stamp(os.fstat(fd)))); self.assess('/',os.fstat(fd))
                parts=[] if pending=='/' else pending.split('/')[1:]; current=''; restart=False
                for i,name in enumerate(parts):
                    self.tick(); current+='/'+name
                    if current not in self.entries:raise CatalogError('unknown chain component: '+current)
                    s=os.stat(name,dir_fd=fd,follow_symlinks=False); self.assess(current,s)
                    e=self.entries[current]
                    if e['kind']=='link':
                        if current in seen:raise CatalogError('alias cycle')
                        seen.add(current)
                        target=os.readlink(name,dir_fd=fd)
                        if target!=e['target']:raise CatalogError('alias target drift')
                        links.append((fd,name,stamp(s)))
                        base=target if target.startswith('/') else posixpath.join(posixpath.dirname(current),target)
                        pending=posixpath.normpath(posixpath.join(base,*parts[i+1:]))
                        restart=True;break
                    flags=os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK
                    if e['kind']=='dir':flags|=os.O_DIRECTORY
                    child=os.open(name,flags,dir_fd=fd)
                    after=os.fstat(child);held.append((child,stamp(after)))
                    if stamp(s)!=stamp(after):raise CatalogError('entry/open race')
                    self.assess(current,after);fd=child
                    if i<len(parts)-1 and e['kind']!='dir':raise CatalogError('non-directory component')
                if not restart:
                    final=fd;break
                if len(seen)>len(self.entries):raise CatalogError('alias chain bound')
            yield final,current or '/',self.entries[current or '/']
            for fd,name,before in links:
                if stamp(os.stat(name,dir_fd=fd,follow_symlinks=False))!=before:raise CatalogError('alias changed during read')
            for fd,before in held:
                if stamp(os.fstat(fd))!=before:raise CatalogError('entry changed during read')
        finally:
            for fd,_ in reversed(held):os.close(fd)

    def pin(self,path):
        with self.opened(path) as (fd,canonical,e):
            if e['kind']!='file':raise CatalogError('not regular file')
            self.files+=1
            if self.files>self.bounds['files'] or self.used+e['size']>self.bounds['bytes']:
                raise CatalogError('file/byte bound')
            h=hashlib.sha256(); left=e['size']
            while left:
                self.tick(); chunk=os.read(fd,min(CHUNK,left))
                if not chunk:raise CatalogError('short read')
                left-=len(chunk);self.used+=len(chunk);h.update(chunk)
            if os.read(fd,1):raise CatalogError('file grew beyond planned size')
            return dict(sha256=h.hexdigest(),size=e['size'],canonical=canonical)

    def inventory(self,roots):
        result={}; visited=set()
        def visit(path):
            self.tick()
            with self.opened(path) as (fd,canonical,e):
                if e['kind']=='file':
                    result[path]=self.pin(path);return
                if e['kind']!='dir' or canonical in visited:raise CatalogError('directory cycle/duplicate root')
                visited.add(canonical)
                expected=e['children']  # absent means ancestor-only, never traversable
                if len(expected)>self.bounds['files']:raise CatalogError('directory entry bound')
                names=[]
                with os.scandir(fd) as entries:
                    for entry in entries:
                        self.tick();names.append(entry.name)
                        if len(names)>len(expected):raise CatalogError('unknown directory entry')
                if sorted(names)!=sorted(expected) or len(names)!=len(set(names)):
                    raise CatalogError('directory membership drift')
                for name in sorted(names):
                    if name in ('.','..') or '/' in name:raise CatalogError('invalid child')
                    visit(canonical.rstrip('/')+'/'+name)
        for root in roots:visit(root)
        return result
