"""In-memory synthetic filesystem only. No real filesystem/native operations."""
import errno
import os
import stat
from types import SimpleNamespace

class FS:
    def __init__(self):
        self.nodes={};self.handles={};self.nextfd=10;self.nextino=100;self.events=[];self.onread=None
        self.add('/',stat.S_IFDIR|0o755)
    def add(self,path,mode,data=b'',target=None,uid=0,gid=0,nlink=1):
        self.nextino+=1
        n=SimpleNamespace(st_dev=1,st_ino=self.nextino,st_mode=mode,st_uid=uid,st_gid=gid,st_nlink=nlink,
                          st_size=len(data),st_mtime_ns=1,st_ctime_ns=1,data=data,target=target)
        self.nodes[path]=n;return n
    def path(self,path,dir_fd=None):
        if path.startswith('/'):return path
        return self.handles[dir_fd]['path'].rstrip('/')+'/'+path
    def open(self,path,flags,mode=0o777,dir_fd=None):
        p=self.path(path,dir_fd);n=self.nodes.get(p)
        if flags&os.O_CREAT:
            if n is not None and flags&os.O_EXCL:raise FileExistsError(p)
            if n is None:n=self.add(p,stat.S_IFREG|mode)
        if n is None:raise FileNotFoundError(p)
        if flags&os.O_NOFOLLOW and stat.S_ISLNK(n.st_mode):raise OSError(errno.ELOOP,'nofollow')
        if flags&os.O_DIRECTORY and not stat.S_ISDIR(n.st_mode):raise NotADirectoryError(p)
        self.nextfd+=1;fd=self.nextfd;self.handles[fd]=dict(node=n,path=p,pos=0,flags=flags)
        self.events.append(('open',p,fd,flags));return fd
    def dup(self,fd):
        h=self.handles[fd];self.nextfd+=1;self.handles[self.nextfd]=dict(h);return self.nextfd
    def close(self,fd):self.events.append(('close',fd));del self.handles[fd]
    def fstat(self,fd):return SimpleNamespace(**vars(self.handles[fd]['node']))
    def stat(self,path,dir_fd=None,follow_symlinks=False):return SimpleNamespace(**vars(self.nodes[self.path(path,dir_fd)]))
    def readlink(self,path,dir_fd=None):return self.nodes[self.path(path,dir_fd)].target
    def mkdir(self,path,mode,dir_fd=None):
        p=self.path(path,dir_fd)
        if p in self.nodes:raise FileExistsError(p)
        self.add(p,stat.S_IFDIR|mode)
    def read(self,fd,size):
        if self.onread:self.onread(self,fd)
        h=self.handles[fd];b=h['node'].data[h['pos']:h['pos']+size];h['pos']+=len(b);return b
    def write(self,fd,b):
        h=self.handles[fd];n=h['node'];n.data=n.data[:h['pos']]+b+n.data[h['pos']+len(b):];h['pos']+=len(b);n.st_size=len(n.data)
        self.events.append(('write',fd,len(b)));return len(b)
    def fsync(self,fd):self.events.append(('fsync',fd))
    def fchmod(self,fd,mode):
        # Filesystem mock rejects sealing with ANY active writer, including an
        # old untrusted staging writer if it were accidentally adopted.
        assert not any(h['flags']&os.O_ACCMODE in (os.O_WRONLY,os.O_RDWR) for h in self.handles.values())
        n=self.handles[fd]['node'];n.st_mode=stat.S_IFMT(n.st_mode)|mode;n.st_ctime_ns+=1
        self.events.append(('seal',fd,mode))
    def listdir(self,fd):
        p=self.handles[fd]['path'].rstrip('/')+'/'
        return [x[len(p):] for x in self.nodes if x.startswith(p) and '/' not in x[len(p):] and x!=p]
    def lseek(self,fd,pos,whence):self.handles[fd]['pos']=pos
