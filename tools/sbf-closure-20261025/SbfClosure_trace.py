"""Strict bounded subset of actual strace text; unknown syntax/syscalls DENY.

Not a general strace parser or a claim that Cargo traces already pass. Capture
must include close/dup/fcntl/fchdir as well as %file,%process; no read/write buffers
or environment dump. -qq suppresses exit summaries, so exit_group is required.
Unfinished/resumed lines, CLONE_FS/FILES, execveat, pid reordering, mmap file IO
without a prior observed sealed open, directory enumeration and arbitrary *at
mutations are intentionally unsupported. Reject them, never normalize away gaps.
"""
import copy, json, posixpath, re

class TraceDenied(ValueError):pass

def check(ok,why):
    if not ok:raise TraceDenied(why)

def split(s):
    out=[];start=0;depth=0;quoted=False;escape=False
    for i,c in enumerate(s):
        if quoted:
            if escape:escape=False
            elif c=='\\':escape=True
            elif c=='"':quoted=False
        elif c=='"':quoted=True
        elif c in '([{':depth+=1
        elif c in ')]}':depth-=1;check(depth>=0,'unbalanced args')
        elif c==',' and depth==0:out.append(s[start:i].strip());start=i+1
    check(not quoted and depth==0,'unfinished argument');return out+[s[start:].strip()]

def string(s):
    # JSON-compatible C-string subset only. Octal/hex escapes reject, not guess.
    check(s.startswith('"') and s.endswith('"'),'path truncated/nonstring')
    try:v=json.loads(s)
    except ValueError:raise TraceDenied('unsupported C-string escape')
    check(isinstance(v,str) and '\x00' not in v,'invalid path');return v

class Join:
    def __init__(self,root_pid,cwd,seals,outputs):
        check(cwd.startswith('/'),'absolute initial cwd')
        self.p={root_pid:dict(cwd=cwd,fds={},alive=True)};self.seals=seals
        self.outputs=set(outputs);self.joined=[];self.execs=[];self.created=set();self.lines=0
        # Exact per-file pre/GO/post pins, not a boolean "trusted input" premise.
        for path,row in seals.items():
            check(path.startswith('/') and posixpath.normpath(path)==path,'seal path')
            check(row['physical'].startswith('/') and row['type'] in ('regular','directory','symlink'),'seal mapping')
            check(row['pre']==row['go']==row['post'],'input identity drift')
            if row['type']=='regular':check(len(row['pre']['sha256'])==64 and row['pre']['bytes']>=0,'file identity')
    def path(self,p,s,dirfd='AT_FDCWD'):
        value=string(s)
        if value.startswith('/'):raw=value
        elif dirfd=='AT_FDCWD':raw=p['cwd']+'/'+value
        else:
            check(dirfd.isdigit() and int(dirfd) in p['fds'],'unknown/closed dirfd')
            base,_,directory=p['fds'][int(dirfd)];check(directory,'nondirectory dirfd');raw=base+'/'+value
        # Walk components including symlinks BEFORE resolving .., not normpath first.
        todo=raw.split('/');parts=[];links=0
        while todo:
            c=todo.pop(0)
            if c in ('','.'):continue
            if c=='..':
                if parts:parts.pop()
                continue
            parts.append(c);at='/'+ '/'.join(parts);row=self.seals.get(at)
            if row and row['type']=='symlink':
                links+=1;check(links<=40,'symlink loop');target=row['pre']['link']
                parts.pop()
                if target.startswith('/'):parts=[]
                todo=target.split('/')+todo
        return '/'+ '/'.join(parts)
    def input(self,path,success):
        if path in self.created:
            self.joined.append(dict(path=path,kind='fresh-output',success=success));return
        row=self.seals.get(path)
        if row:
            self.joined.append(dict(path=path,physical=row['physical'],identity=row['pre'],success=success));return
        # Failed probes must also be explicitly sealed as absent from a root
        # exact-directory membership manifest, never allowed just because ENOENT.
        raise TraceDenied('unsealed input or failed probe '+path)
    def line(self,line):
        self.lines+=1;check(self.lines<=1_000_000 and len(line)<=131072,'trace bounds')
        check(not any(s in line for s in ('<unfinished','resumed>','???','strace:','...','+++','---')),'truncated/lost/unsupported record')
        m=re.fullmatch(r'(\d+) (\d+\.\d+) ([a-zA-Z0-9_]+)\((.*)\) += (.+)',line)
        check(m is not None,'unknown line format')
        pid=int(m[1]);check(pid in self.p and self.p[pid]['alive'],'unknown/dead descendant')
        p=self.p[pid];call=m[3];a=split(m[4]);ret=m[5]
        ok=not ret.startswith('-1 ')
        num=re.match(r'-?\d+',ret)
        n=int(num[0]) if num else None
        if call in ('clone','clone3','fork','vfork'):
            check('CLONE_FS' not in m[4] and 'CLONE_FILES' not in m[4] and 'CLONE_THREAD' not in m[4],'shared process state unsupported')
            if ok:
                check(n is not None and n>0 and n not in self.p,'invalid child pid')
                self.p[n]=copy.deepcopy(p)
        elif call=='execve':
            path=self.path(p,a[0]);self.input(path,ok)
            check(len(a)==3 and a[1].startswith('[') and re.fullmatch(r'0x[0-9a-f]+ /\* \d+ vars \*/',a[2]),'exec argv/env truncated or exposed')
            argv=[string(x) for x in split(a[1][1:-1])];check(argv,'empty exec argv')
            if ok:
                check(n==0,'exec result');self.execs.append(dict(pid=pid,path=path,argv=argv))
                p['fds']={k:v for k,v in p['fds'].items() if not v[1]}
        elif call in ('open','openat'):
            offset=1 if call=='openat' else 0
            path=self.path(p,a[offset],a[0] if offset else 'AT_FDCWD');flags=a[offset+1]
            writing=any(x in flags for x in ('O_WRONLY','O_RDWR','O_CREAT','O_TRUNC','O_APPEND'))
            if writing:
                check(path in self.outputs,'write outside exact fresh output allowlist')
                if ok:self.created.add(path)
            else:self.input(path,ok)
            if ok:
                check(n is not None and n>=0 and n not in p['fds'],'FD collision/unknown inherited FD')
                p['fds'][n]=(path,'O_CLOEXEC' in flags,'O_DIRECTORY' in flags)
        elif call=='close':
            check(a[0].isdigit(),'close FD');fd=int(a[0])
            check(fd in p['fds'] or fd in (0,1,2),'unknown/inherited close')
            if ok:p['fds'].pop(fd,None)
        elif call in ('dup','dup2','dup3'):
            check(a[0].isdigit() and int(a[0]) in p['fds'],'unknown dup source')
            if ok:
                check(n is not None and n>=0,'dup result');path,_,directory=p['fds'][int(a[0])]
                p['fds'][n]=(path,call=='dup3' and 'O_CLOEXEC' in a[-1],directory)
        elif call=='fcntl':
            check(a[0].isdigit() and int(a[0]) in p['fds'],'unknown fcntl FD')
            check(a[1]=='F_SETFD' and a[2] in ('FD_CLOEXEC','0'),'unsupported fcntl')
            if ok:
                path,_,directory=p['fds'][int(a[0])];p['fds'][int(a[0])]=(path,a[2]=='FD_CLOEXEC',directory)
        elif call=='chdir':
            path=self.path(p,a[0]);self.input(path,ok)
            if ok:p['cwd']=path
        elif call=='fchdir':
            check(a[0].isdigit() and int(a[0]) in p['fds'],'unknown fchdir FD')
            path,_,directory=p['fds'][int(a[0])];check(directory,'fchdir non-directory')
            if ok:p['cwd']=path
        elif call in ('access','stat','lstat','readlink','newfstatat','faccessat','faccessat2','readlinkat','statx'):
            at=call in ('newfstatat','faccessat','faccessat2','readlinkat','statx')
            path=self.path(p,a[1] if at else a[0],a[0] if at else 'AT_FDCWD');self.input(path,ok)
            # readlink content must agree with sealed symlink, no unchecked target.
            if call in ('readlink','readlinkat') and ok:
                raw=string(a[1] if not at else a[2]);row=self.seals.get(path)
                check(row and row['type']=='symlink' and row['pre']['link']==raw,'readlink mismatch or normalized link')
        elif call in ('exit','exit_group'):
            check(a==['0'] and ret=='?','nonzero/unknown process exit');p['alive']=False
        else:raise TraceDenied('unsupported syscall '+call)
    def finish(self):
        check(all(not p['alive'] for p in self.p.values()),'lost live descendants')
        return dict(status='ACCEPTED STRICT SUBSET ONLY',records=self.lines,inputs=self.joined,execs=self.execs,
            fresh_outputs=sorted(self.created),limitations='No actual trace consumed; pre/GO/post seals must come from reviewed immutable rootfs producer. Does not establish syscall memory effects, compiler correctness, full IO or semantic refinement. All unsupported strace features fail closed.')
