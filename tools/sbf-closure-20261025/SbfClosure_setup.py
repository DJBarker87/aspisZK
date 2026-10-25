"""Review-only Linux setup for ONE tiny Python probe, never a compiler.

No CLI execution path in this phase. approved_manifest_sha256 must be populated
by a later reviewed source commit. No arbitrary root/uid/argv/path arguments.
Copies individual public files into root-owned synthetic root: RO bind alone
would not exclude same-uid host writers. No actual setup has run.
"""
import ctypes, hashlib, json, os, pathlib, posixpath, stat

STAGE = '/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024'
OWN = STAGE + '/SbfClosure-20261025-probe-v1'
ROOT = OWN + '/rootfs'
APPROVED_MANIFEST_SHA256 = ()  # Empty: fail closed; no privileged execution authority.
PROBE = ('/usr/bin/python3', '-I', '-S', '-B', '-c',
    'import os,json;assert os.getresuid()==(1000,)*3;'
    'assert os.getresgid()==(1000,)*3;assert os.getgroups()==[];'
    'print(json.dumps({"SbfClosure":"tiny probe only","pid":os.getpid()}))')
ENV = {'PATH':'/usr/bin:/bin','LC_ALL':'C','HOME':'/home/dombarker','TMPDIR':'/tmp'}
NS = 0x00020000 | 0x20000000 | 0x40000000  # mount, PID, net; no user/cgroup ns
MS_BIND, MS_REC, MS_PRIVATE, MS_REMOUNT, MS_RDONLY = 4096, 16384, 1<<18, 32, 1
MS_NOSUID, MS_NODEV, MS_NOEXEC = 2, 4, 8

class Denied(RuntimeError):
    pass

def require(ok, message):
    if not ok: raise Denied(message)

def canonical(s):
    require(isinstance(s,str) and s.startswith('/') and s!='/' and '\x00' not in s,
            'absolute nonroot path required')
    require(posixpath.normpath(s)==s and '//' not in s, 'noncanonical path')
    return s

def validate(m, approved):
    raw=(json.dumps(m,sort_keys=True,separators=(',',':'))+'\n').encode()
    require(hashlib.sha256(raw).hexdigest() in approved,'unreviewed exact manifest')
    require(m['root']==ROOT and m['own']==OWN,'wrong own root')
    require(m['uid']==m['gid']==1000,'wrong uid/gid')
    require(tuple(m['argv'])==PROBE and m['env']==ENV,'argv/env outside tiny probe')
    require(m['scope']['swap_max']==0 and m['scope']['tasks_max']<=64,'scope bounds')
    require(0<m['scope']['memory_high']<=6*1024**3 and
            m['scope']['memory_high']<=m['scope']['memory_max']<=8*1024**3,'memory bounds')
    names=set()
    for r in m['files']:
        p=canonical(r['logical']); source=canonical(r['physical'])
        require(p not in names,'duplicate logical file'); names.add(p)
        require(r['type'] in ('regular','symlink'), 'only finite individual public files/links')
        require(not int(r['mode']) & ~0o777,'special permission bits')
        require(r['public_kind'] in ('frozen-source','registry','platform','SDK','native','runtime','outer-tool','synthesized-public'),'unreviewed input class')
        # Physical source constrained by exact signed-off manifest hash, not user argv.
        if r['type']=='regular':
            require(len(r['sha256'])==64 and 0<=r['bytes']<=512*1024**2,'file seal')
        else:
            require('\x00' not in r['link'],'link NUL')
    for r in m['files']:
        if r['type']=='symlink':
            target=posixpath.normpath(posixpath.join(posixpath.dirname(r['logical']),r['link']))
            require(target in names,'symlink target outside exact allowlist')
    require(set(m['devices'])=={'null','zero','urandom'},'device allowlist')
    require(set(m['writable'])=={'/tmp','/home/dombarker/.probe-work'},'probe writable view')
    require(m['go']['parent_pid']>1 and len(m['go']['receipt_sha256'])==64,'host GO binding')

def prepare(m, ops, approved=APPROVED_MANIFEST_SHA256):
    """Testable ordered program; every check before next irreversible operation.

    Backend exceptions terminate namespace child. No global cleanup/umount,
    recursive deletion, key operations or fallback to host execution.
    """
    validate(m,approved)
    ops.host_gate(m)  # host parent PID/start/cgroup + exact receipt + current caps
    before=ops.namespaces()
    ops.unshare(NS)   # failure raises; absolutely no mount before this
    # CLONE_NEWPID applies to the child only. Parent must exit/wait, never build.
    ops.fork_guest()
    after=ops.namespaces()
    require(all(before[k]!=after[k] for k in ('mnt','net','pid')),'namespace identity unchanged')
    ops.mount(None,'/',None,MS_REC|MS_PRIVATE,None)
    ops.create_root(m) # exclusive root-owned inode; pinned dirfd, never chroot by raced path
    for r in m['files']:
        ops.copy_sealed(r) # regular: O_NOFOLLOW/openat all ancestors, stat+hash before/after
    ops.make_links(m['files'])
    ops.mount(ROOT,ROOT,None,MS_BIND,None)
    ops.mount(None,ROOT,None,MS_BIND|MS_REMOUNT|MS_RDONLY|MS_NOSUID|MS_NODEV,None)
    ops.assert_mount(ROOT,True)
    for logical in m['writable']:
        ops.mount(OWN+'/rw'+logical,ROOT+logical,None,MS_BIND,None)
        ops.assert_mount(ROOT+logical,False)
    ops.mount('proc',ROOT+'/proc','proc',MS_NOSUID|MS_NODEV|MS_NOEXEC,None)
    ops.assert_private_proc()
    ops.devices(m['devices'])
    ops.close_fds_and_stdio() # no secret/socket stream; only own receipt files and null
    ops.chroot_fd()
    ops.drop_all(1000,1000) # groups, bounding, ambient, real/effective/saved IDs, capset, NNP
    ops.assert_child(m)
    ops.exec(PROBE,ENV)
    raise Denied('exec unexpectedly returned')

class Linux:
    """Literal backend, unavailable from CLI. No trusted-producer boolean stub."""
    def __init__(self):
        self.libc=ctypes.CDLL(None,use_errno=True); self.rootfd=None
    def call(self,name,*args):
        result=getattr(self.libc,name)(*args)
        if result<0: raise OSError(ctypes.get_errno(),name)
        return result
    def namespaces(self):
        return {k:os.readlink('/proc/self/ns/'+k) for k in ('mnt','net','pid')}
    def host_gate(self,m):
        require(os.getresuid()==(0,0,0),'privileged setup parent required')
        require(os.getppid()==m['go']['parent_pid'],'wrong actual host parent')
        p='/proc/'+str(os.getppid())
        start=pathlib.Path(p+'/stat').read_text().rsplit(')',1)[1].split()[19]
        require(start==str(m['go']['parent_start_ticks']),'parent start mismatch')
        cg=pathlib.Path('/proc/self/cgroup').read_text()
        require(cg==pathlib.Path(p+'/cgroup').read_text()==m['go']['cgroup'],'same actual scope required')
        require(cg.startswith('0::/') and len(cg.splitlines())==1,'cgroupv2 required')
        base='/sys/fs/cgroup'+cg.strip()[3:]
        for n,k in [('memory.max','memory_max'),('memory.high','memory_high'),('memory.swap.max','swap_max'),('pids.max','tasks_max')]:
            require(pathlib.Path(base+'/'+n).read_text().strip()==str(m['scope'][k]),'changed scope '+n)
        # Exact receipt path/bytes are reviewed manifest members; no arbitrary GO input.
        r=self.read_regular(m['go']['receipt_path'])
        require(hashlib.sha256(r).hexdigest()==m['go']['receipt_sha256'],'GO receipt seal')
        # Producer schema validation/GO freshness not invented here. No approved manifest
        # may be issued until ResourceAdmit-v2 schema/producer integration is reviewed.
        raise Denied('ResourceAdmit-v2 actual GO schema/freshness integration still blocked')
    def unshare(self,flags): self.call('unshare',flags)
    def fork_guest(self):
        pid=os.fork()
        if pid:
            _,status=os.waitpid(pid,0); os._exit(os.waitstatus_to_exitcode(status))
    def mount(self,source,target,fstype,flags,data):
        def enc(x): return None if x is None else x.encode()
        self.call('mount',enc(source),enc(target),enc(fstype),ctypes.c_ulong(flags),enc(data))
    def open_regular(self,path):
        # O_NOFOLLOW every ancestor (no resolve()/open TOCTOU). Return pinned file fd.
        canonical(path); d=os.open('/',os.O_RDONLY|os.O_DIRECTORY)
        try:
            parts=path.split('/')[1:]
            for part in parts[:-1]:
                n=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=d)
                os.close(d); d=n
            f=os.open(parts[-1],os.O_RDONLY|os.O_NOFOLLOW,dir_fd=d)
            s=os.fstat(f)
            require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular/hardlinked source')
            return f
        finally: os.close(d)
    def read_regular(self,path):
        f=self.open_regular(path)
        try:
            require(os.fstat(f).st_size<=1_000_000,'oversized GO receipt')
            return os.read(f,1_000_001)
        finally:os.close(f)
    def create_root(self,m):
        p=pathlib.Path(STAGE)
        for q in (p,*p.parents):require(not q.is_symlink(),'stage symlink')
        require(p.stat().st_uid==1000 and stat.S_IMODE(p.stat().st_mode)==0o700,'stage ownership/mode')
        require(self.read_regular(STAGE+'/OWNER')==b'SbfRecapturePrep 20261024\n','OWNER')
        os.mkdir(OWN,0o700); os.mkdir(ROOT,0o755)
        self.rootfd=os.open(ROOT,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        require(os.fstat(self.rootfd).st_uid==0,'rootfs not root owned')
        for d in ('proc','dev','tmp','home/dombarker/.probe-work'):
            pathlib.Path(ROOT+'/'+d).mkdir(parents=True,exist_ok=True)
        for d in m['writable']:
            dest=pathlib.Path(OWN+'/rw'+d);dest.mkdir(parents=True)
            os.chown(dest,1000,1000);os.chmod(dest,0o700)
        for n in m['devices']:(pathlib.Path(ROOT+'/dev')/n).touch(mode=0o600)
    def copy_sealed(self,r):
        if r['type']=='symlink':return
        src=self.open_regular(r['physical'])
        try:
            a=os.fstat(src); require(a.st_size==r['bytes'] and stat.S_IMODE(a.st_mode)==r['mode'],'source metadata seal')
            dst=pathlib.Path(ROOT+r['logical']);dst.parent.mkdir(parents=True,exist_ok=True)
            h=hashlib.sha256()
            with dst.open('xb') as out:
                while b:=os.read(src,1024**2):h.update(b);out.write(b)
            b=os.fstat(src)
            require((a.st_dev,a.st_ino,a.st_size,a.st_mtime_ns,a.st_ctime_ns,a.st_mode)==(b.st_dev,b.st_ino,b.st_size,b.st_mtime_ns,b.st_ctime_ns,b.st_mode),'source changed')
            require(h.hexdigest()==r['sha256'],'source content seal')
            os.chmod(dst,r['mode']);require(dst.stat().st_uid==0,'copy not root owned')
        finally:os.close(src)
    def make_links(self,rows):
        for r in rows:
            if r['type']=='symlink':
                p=pathlib.Path(ROOT+r['logical']);p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(r['link'])
    def assert_mount(self,path,ro):
        # No spaces/escaped path permitted by reviewed manifest; exact mountpoint only.
        rows=[line.split() for line in pathlib.Path('/proc/self/mountinfo').read_text().splitlines()]
        hits=[r for r in rows if r[4]==path]
        require(len(hits)==1 and ('ro' in hits[0][5].split(','))==ro,'mount roflag')
        require(not any(r[4].startswith(path+'/') for r in rows),'unexpected source submount')
    def assert_private_proc(self):
        require(os.getpid()==1,'proc must belong to guest PID namespace')
        require(pathlib.Path(ROOT+'/proc/self/ns/pid').readlink()==pathlib.Path('/proc/self/ns/pid').readlink(),'proc namespace mismatch')
    def devices(self,names):
        for name,minor in [('null',3),('zero',5),('urandom',9)]:
            s=os.stat('/dev/'+name); require(stat.S_ISCHR(s.st_mode) and os.major(s.st_rdev)==1 and os.minor(s.st_rdev)==minor,'device identity')
            self.mount('/dev/'+name,ROOT+'/dev/'+name,None,MS_BIND,None)
    def close_fds_and_stdio(self):
        null=os.open('/dev/null',os.O_RDONLY|os.O_NOFOLLOW)
        os.dup2(null,0);os.close(null)
        for fd,name in [(1,'stdout'),(2,'stderr')]:
            f=os.open(OWN+'/'+name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
            os.dup2(f,fd);os.close(f)
        for name in os.listdir('/proc/self/fd'):
            fd=int(name)
            if fd>2 and fd!=self.rootfd:
                try:os.close(fd)
                except OSError:pass
    def chroot_fd(self):
        os.fchdir(self.rootfd);os.chroot('.');os.chdir('/');os.close(self.rootfd)
    def drop_all(self,uid,gid):
        os.umask(0o077);os.setgroups([])
        self.call('prctl',47,4,0,0,0) # PR_CAP_AMBIENT CLEAR_ALL
        # cap_last_cap is kernel data, not a guessed fixed capability count.
        last=int(pathlib.Path('/proc/sys/kernel/cap_last_cap').read_text())
        require(0<=last<64,'capability ABI unsupported')
        for cap in range(last+1):self.call('prctl',24,cap,0,0,0) # bounding drop
        os.setresgid(gid,gid,gid);os.setresuid(uid,uid,uid)
        class Header(ctypes.Structure):_fields_=[('version',ctypes.c_uint32),('pid',ctypes.c_int)]
        class Data(ctypes.Structure):_fields_=[('effective',ctypes.c_uint32),('permitted',ctypes.c_uint32),('inheritable',ctypes.c_uint32)]
        header=Header(0x20080522,0);data=(Data*2)()
        self.call('capset',ctypes.byref(header),ctypes.byref(data))
        self.call('prctl',38,1,0,0,0) # no_new_privs
    def assert_child(self,m):
        require(os.getresuid()==(1000,)*3 and os.getresgid()==(1000,)*3 and os.getgroups()==[],'uid/groups drop')
        s=dict(line.split(':',1) for line in pathlib.Path('/proc/self/status').read_text().splitlines() if ':' in line)
        for k in ('CapInh','CapPrm','CapEff','CapBnd','CapAmb'):require(int(s[k],16)==0,'capability '+k)
        require(s['NoNewPrivs'].strip()=='1','NNP')
        require(pathlib.Path('/proc/self/cgroup').read_text()==m['go']['cgroup'],'child cgroup drift')
        require({int(x) for x in os.listdir('/proc/self/fd')}<={0,1,2,3},'unexpected inherited fd')
        os.environ.clear()
    def exec(self,argv,env): os.execve(argv[0],list(argv),env)

if __name__=='__main__':
    raise SystemExit('SbfClosure: review-only; no execution entry point or approved manifest')
