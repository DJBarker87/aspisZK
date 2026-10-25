"""One focused source fixture pass; synthetic FS, no host/native claims."""
import hashlib
import json
from pathlib import Path
import resource
import runpy
import stat
import sys
import tempfile
import time
from types import SimpleNamespace

START=time.monotonic()
HERE=Path(__file__).resolve().parent
OUT=HERE.parents[1]/'evidence/sbf-runtime-trace-20261025'
paths=runpy.run_path(str(HERE/'SbfRuntimeTrace_paths.py'))
parser=runpy.run_path(str(HERE/'SbfRuntimeTrace_parse.py'))['parse']
checks=[]
def check(name,condition):
    checks.append(dict(name=name,passed=bool(condition)))
    if not condition: raise AssertionError(name)

class FS:
    """Explicit synthetic root identities, no stat rewriting on real files."""
    def __init__(self):
        self.nodes={};self.fds={};self.next=10;self.race=None;self.count={}
        for p in ('/','/usr','/usr/bin','/usr/lib','/usr/local','/usr/local/lib','/home','/home/user','/etc','/etc/ssl'):
            self.add(p,stat.S_IFDIR|0o755)
        self.add('/usr/lib/end',stat.S_IFREG|0o444)
    def add(self,path,mode,target=None,uid=0):
        self.nodes[path]=(SimpleNamespace(st_dev=1,st_ino=len(self.nodes)+1,st_mode=mode,st_uid=uid,
                            st_gid=0,st_nlink=1,st_size=1,st_mtime_ns=1,st_ctime_ns=1),target)
    def link(self,path,target): self.add(path,stat.S_IFLNK|0o777,target)
    def stat(self,name,dir_fd=None,follow_symlinks=False):
        path=name if name.startswith('/') else self.fds[dir_fd].rstrip('/')+'/'+name
        if path not in self.nodes: raise FileNotFoundError(2,'synthetic missing',path)
        self.count[path]=self.count.get(path,0)+1
        row=self.nodes[path][0]
        if self.race==path and self.count[path]>1:
            d=vars(row).copy();d['st_ctime_ns']+=1;return SimpleNamespace(**d)
        return row
    def open(self,name,flags,dir_fd=None):
        path=name if name.startswith('/') else self.fds[dir_fd].rstrip('/')+'/'+name
        if path not in self.nodes: raise FileNotFoundError(2,'synthetic missing',path)
        self.next+=1;self.fds[self.next]=path;return self.next
    def fstat(self,fd): return self.nodes[self.fds[fd]][0]
    def close(self,fd): del self.fds[fd]
    def readlink(self,name,dir_fd): return self.nodes[self.fds[dir_fd].rstrip('/')+'/'+name][1]

def attempt(label,path,setup,success,contains=None):
    fs=FS();setup(fs);rows=[]
    try:
        physical,s,row=paths['walk'](path,rows,fs)
        check(label+' accepted',success and physical=='/usr/lib/end')
    except (ValueError,OSError) as exc:
        check(label+' rejected',not success)
        check(label+' failure retained',len(rows)==1 and rows[0]['status']=='FAILED' and rows[0]['error_type']==type(exc).__name__)
        if contains: check(label+' reason',contains in rows[0]['error'])
    check(label+' descriptors closed',not fs.fds)
    return rows

error=None
try:
    # Resolve the real temporary fixture destination; no production ownership
    # assertion is bypassed to treat writable /tmp as a trusted host root.
    with tempfile.TemporaryDirectory(prefix='SbfRuntimeTrace-') as tmp:
        destination=Path(tmp).resolve()
        (destination/'fixture-description.json').write_text('{"kind":"synthetic root-owned FS"}\n')
        check('resolved temporary fixture destination',destination.is_absolute() and destination.is_dir())
        attempt('direct','/usr/lib/end',lambda f:None,True)
        attempt('relative','/usr/lib/a',lambda f:f.link('/usr/lib/a','end'),True)
        attempt('absolute','/usr/bin/a',lambda f:f.link('/usr/bin/a','/usr/lib/end'),True)
        def aliases(f):
            f.link('/lib64','/usr/lib64');f.link('/usr/lib64','/usr/lib');f.link('/usr/lib/loader','end')
        attempt('usr-lib64 intermediate','/lib64/loader',aliases,True)
        attempt('lib intermediate','/lib/end',lambda f:f.link('/lib','usr/lib'),True)
        attempt('escape','/usr/lib/a',lambda f:f.link('/usr/lib/a','/home/user/end'),False,'outside')
        attempt('user-root','/home/user/end',lambda f:None,False,'outside')
        attempt('loop','/usr/lib/a',lambda f:f.link('/usr/lib/a','a'),False,'loop')
        def depth(f):
            for i in range(17): f.link('/usr/lib/a'+str(i),'a'+str(i+1) if i<16 else 'end')
        attempt('depth','/usr/lib/a0',depth,False,'depth')
        attempt('ownership','/usr/lib/end',lambda f:setattr(f.nodes['/usr/lib'][0],'st_uid',1000),False,'non-root')
        attempt('writable','/usr/lib/end',lambda f:setattr(f.nodes['/usr/lib'][0],'st_mode',stat.S_IFDIR|0o775),False,'writable')
        attempt('symlink ownership','/usr/lib/a',lambda f:(f.link('/usr/lib/a','end'),setattr(f.nodes['/usr/lib/a'][0],'st_uid',1000)),False,'non-root')
        attempt('race','/usr/lib/a',lambda f:(f.link('/usr/lib/a','end'),setattr(f,'race','/usr/lib/a')),False,'drift')
        missing=attempt('missing','/lib64/missing',aliases,False,'missing')
        check('ENOENT and partial chain explicit',missing[0]['errno']==2 and missing[0]['failed_component']=='/usr/lib/missing' and len(missing[0]['symlinks'])==2)
        attempt('alias endpoint disallowed','/lib64',lambda f:f.add('/lib64',stat.S_IFDIR|0o755),False,'final endpoint')
        attempt('lexical dotdot','/usr/lib/../end',lambda f:None,False,'components')
        # Trace source fixture, PID and timestamp and full descriptor lifecycle.
        start='7 1.000001 execve("/usr/bin/python3", ["/usr/bin/python3"], 0x123 /* 0 vars */) = 0\n'
        end='7 1.100000 +++ exited with 0 +++\n'
        lines=['openat(AT_FDCWD, "/etc/ld.so.cache", O_RDONLY|O_CLOEXEC) = 3</etc/ld.so.cache>',
               'fcntl(3</etc/ld.so.cache>, F_GETFD) = 0x1 (flags FD_CLOEXEC)',
               'dup(3</etc/ld.so.cache>) = 4</etc/ld.so.cache>',
               'dup2(4</etc/ld.so.cache>, 5) = 5</etc/ld.so.cache>',
               'dup3(5</etc/ld.so.cache>, 6, O_CLOEXEC) = 6</etc/ld.so.cache>',
               'fcntl(6</etc/ld.so.cache>, F_DUPFD_CLOEXEC, 7) = 7</etc/ld.so.cache>',
               'close(3</etc/ld.so.cache>) = 0',
               'close(4</etc/ld.so.cache>) = 0',
               'close(5</etc/ld.so.cache>) = 0',
               'close(6</etc/ld.so.cache>) = 0',
               'close(7</etc/ld.so.cache>) = 0',
               'access("/etc/ld.so.preload", R_OK) = -1 ENOENT (No such file or directory)']
        trace=start+''.join('7 1.010000 '+x+'\n' for x in lines)+end
        p=parser(trace,7)
        check('descriptor lifecycle complete',p['complete'])
        check('opened unmapped cache retained',p['opened_unmapped']==['/etc/ld.so.cache'])
        check('negative probes retained',p['negatives'][0]['errno']=='ENOENT')
        split=start+'7 1.010000 openat(AT_FDCWD, "/usr/lib/end", O_RDONLY <unfinished ...>\n7 1.020000 <... openat resumed>) = 3</usr/lib/end>\n'+end
        p=parser(split,7)
        check('unfinished resumed reconstruction',p['complete'] and len(p['events'])==4 and p['events'][2]['resumes']==1)
        for label,body in {
            'unpaired':'7 1.010000 openat(AT_FDCWD, "/usr/lib/end", O_RDONLY <unfinished ...>\n',
            'resumed mismatch':'7 1.010000 <... close resumed>) = 0\n',
            'unknown syscall':'7 1.010000 magiccall() = 0\n',
            'unknown dirfd':'7 1.010000 openat(9, "end", O_RDONLY) = 3\n',
            'CLONE_FILES':'7 1.010000 clone(CLONE_FILES) = 8\n',
            'unknown mmap fd':'7 1.010000 mmap(NULL, 100, PROT_READ, MAP_PRIVATE, 9, 0) = 0x1000\n',
            'unexpected pid':'8 1.010000 close(0) = 0\n',
            'write open':'7 1.010000 openat(AT_FDCWD, "/usr/lib/end", O_WRONLY) = 3\n',
            'second exec':'7 1.010000 execve("/usr/bin/python3", [], NULL) = 0\n',
        }.items():
            p=parser(start+body+end,7)
            check(label+' denies completeness',not p['complete'] and len(p['events'])==3)
        reused=json.loads((OUT/'SbfRuntimeTrace-reused-fixtures.json').read_text())
        for name,item in reused['fixtures'].items():
            p=parser(item['line']+'\n')
            check('reused real example '+name+' retained denied',not p['complete'] and p['events'][0]['raw']==item['line'])
except BaseException as exc:
    error=dict(type=type(exc).__name__,message=str(exc))
finally:
    def pin(raw): return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
    receipt=dict(target='new finite chain/parser source fixtures only',exit=1 if error else 0,error=error,
        checks=checks,argv=getattr(sys,'orig_argv',sys.argv),argv_source='sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv',
        source_revision=(OUT/'SbfRuntimeTrace-entry.txt').read_text().strip(),
        wall_seconds=time.monotonic()-START,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap_operations=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,aggregate_rss='UNOBSERVED; tiny local fixture process',axioms='N/A',
        sourcepins={p.name:pin(p.read_bytes()) for p in HERE.iterdir() if p.is_file()},
        dependencies={n:dict(file=getattr(m,'__file__',None),pin=pin(Path(m.__file__).read_bytes()) if getattr(m,'__file__',None) and Path(m.__file__).is_file() else None) for n,m in sorted(sys.modules.items()) if m is not None})
    (OUT/'SbfRuntimeTrace-fixtures-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(exit=receipt['exit'],checks=len(checks),error=error)))
raise SystemExit(1 if error else 0)
