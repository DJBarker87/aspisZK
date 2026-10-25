"""Only text/hash/AST and explicit in-memory synthetic effects. No native imports."""
import ast
import copy
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import resource
import signal
import stat
import sys
import time
import types
import unittest
from unittest.mock import patch
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))  # local synthetic validation only; no privileged loader
from SbfFinite_fixed import RUNTIME, SCHEMA, CATALOG, ARGV, ROOT
from SbfFinite_validate import validate,validate_fixed
from SbfFiniteLinux_capture import Denied,identity,PublicOutput
from SbfFinite_install import Source,Tree,LiteralSource
from SbfFinite_mock import FS
import SbfFiniteRss_sources as sources

RESULTS=[]
def digest(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def selected(filename,names,env):
    text=(H/filename).read_text();tree=ast.parse(text)
    nodes=[n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in names]
    assert {n.name for n in nodes}==set(names)
    exec(compile(ast.Module(body=nodes,type_ignores=[]),'synthetic-selected-'+filename,'exec'),env)
    return env

def setup(alias=False):
    fs=FS();fs.add('/src',stat.S_IFDIR|0o755);fs.add('/src/f',stat.S_IFREG|0o644,b'abc')
    fs.add('/dest',stat.S_IFDIR|0o700)
    paths=['/','/src','/src/f'];path='/src/f'
    if alias:
        fs.add('/alias',stat.S_IFLNK|0o777,target='/src')
        paths=['/','/alias','/','/src','/src/f'];path='/alias/f'
    chain=[dict(path=p,identity=list(identity(fs.nodes[p])),**({'target':fs.nodes[p].target} if stat.S_ISLNK(fs.nodes[p].st_mode) else {})) for p in paths]
    row=dict(path=path,physical='/src/f',size=3,sha256=digest(b'abc')['sha256'],chain=chain)
    return fs,row

class InstallerTests(unittest.TestCase):
    def test_exact_schema_and_all92_bindings(self):
        self.assertEqual(validate_fixed(),RUNTIME)
        for key,val in [('schema','wrong'),('root','/wrong'),('argv',['/bin/sh']),('hash','0'*64),('size',1),('duplicate',None),('copybound',None)]:
            v=dict(schema=SCHEMA,runtime=copy.deepcopy(RUNTIME))
            if key=='schema':v['schema']=val
            elif key in ('root','argv'):v['runtime'][key]=val
            elif key=='hash':v['runtime']['files'][0]['sha256']=val
            elif key=='size':v['runtime']['files'][0]['size']=val
            elif key=='duplicate':v['runtime']['files'][1]=copy.deepcopy(v['runtime']['files'][0])
            else:v['runtime']['files'][0]['size']=64*2**20
            with self.subTest(key=key),self.assertRaises(Denied):validate(v)
    def test_exclusive_alias_clone_closed_writer_readback_seal(self):
        fs,row=setup(True);root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY)
        s=Source(row,fs);t=Tree(root,fs)
        t.copy(s,'/a',dict(digest(b'abc'),mode=0o444));s.close()
        s=Source(row,fs);t.copy(s,'/b',dict(digest(b'abc'),mode=0o444));s.close()
        self.assertNotEqual(fs.nodes['/dest/a'].st_ino,fs.nodes['/dest/b'].st_ino)
        self.assertEqual(t.total,6);self.assertFalse(t.writers);t.seal()
        self.assertEqual(stat.S_IMODE(fs.nodes['/dest/a'].st_mode),0o444)
        writes=[i for i,e in enumerate(fs.events) if e[0]=='write'];seals=[i for i,e in enumerate(fs.events) if e[0]=='seal']
        self.assertLess(max(writes),min(seals));t.close();fs.close(root)
    def test_unadmitted_chain_alias_cycle_and_drift(self):
        for variant in ('target','missing','cycle','uid','mode','race'):
            fs,row=setup(True)
            if variant=='target':fs.nodes['/alias'].target='/other'
            elif variant=='missing':row['chain'].pop(3)
            elif variant=='cycle':row['chain'][1]['target']='/alias';fs.nodes['/alias'].target='/alias'
            elif variant=='uid':fs.nodes['/src/f'].st_uid=9
            elif variant=='mode':fs.nodes['/src'].st_mode|=0o002
            with self.subTest(variant=variant):
                if variant=='race':
                    s=Source(row,fs);fs.nodes['/alias'].st_ctime_ns+=1
                    with self.assertRaises(Denied):s.audit()
                    s.close()
                else:
                    with self.assertRaises((Denied,KeyError)):Source(row,fs)
    def test_wrong_hash_growth_size_and_partial_retained(self):
        for variant in ('hash','growth','shrink','race','readback'):
            fs,row=setup();root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY);t=Tree(root,fs);s=Source(row,fs)
            p=dict(digest(b'abc'),mode=0o444)
            if variant=='hash':p['sha256']='0'*64
            if variant=='growth':fs.nodes['/src/f'].data=b'abcd' # growth without stat update still byte-bound
            if variant=='shrink':fs.nodes['/src/f'].data=b'ab'
            if variant=='race':fs.nodes['/src/f'].st_ctime_ns+=1
            if variant=='readback':
                def mutate(api,fd):
                    h=api.handles[fd]
                    if h['path']=='/dest/a':h['node'].data=b'bad'
                fs.onread=mutate
            with self.subTest(variant=variant),self.assertRaises(Denied):t.copy(s,'/a',p)
            self.assertFalse(t.writers)
            if variant!='race':self.assertIn('/dest/a',fs.nodes)
            t.close();s.close();fs.close(root)
    def test_existing_hardlink_nonregular_oldwriter_staging(self):
        for kind in ('existing','hardlink','nonregular','staging'):
            fs,row=setup();root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY);t=Tree(root,fs);s=Source(row,fs)
            if kind in ('existing','staging'):fs.add('/dest/a',stat.S_IFREG|0o600,b'old')
            if kind=='hardlink':fs.add('/dest/a',stat.S_IFREG|0o600,b'old',nlink=2)
            if kind=='nonregular':fs.add('/dest/a',stat.S_IFIFO|0o600)
            writer=fs.open('/dest/a',os.O_WRONLY) if kind=='staging' else None
            with self.subTest(kind=kind),self.assertRaises(FileExistsError):t.copy(s,'/a',dict(digest(b'abc'),mode=0o444))
            self.assertEqual(fs.nodes['/dest/a'].data,b'old' if kind!='nonregular' else b'')
            if writer:fs.close(writer)
            t.close();s.close();fs.close(root)
    def test_copycount_path_size_time_and_writer_bounds(self):
        for variant in ('count','total','path','size','time','writer'):
            fs,row=setup();root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY);s=Source(row,fs);t=Tree(root,fs)
            p=dict(digest(b'abc'),mode=0o444);path='/a'
            if variant=='count':t.files={str(i):{} for i in range(256)}
            if variant=='total':t.total=64*2**20
            if variant=='path':path='/a/../escape'
            if variant=='size':p['size']=16*2**20+1
            if variant=='time':t.started-=111
            if variant=='writer':t.writers.add(999)
            with self.subTest(variant=variant),self.assertRaises(Denied):
                if variant=='writer':t.seal()
                else:t.copy(s,path,p)
            t.writers.discard(999);t.close();s.close();fs.close(root)
    def test_literal_package_bytes_are_copied_not_adopted(self):
        fs,row=setup();root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY);t=Tree(root,fs)
        s=LiteralSource(b'abc',dict(digest(b'abc'),mode=0o444));t.copy(s,'/module.py',dict(digest(b'abc'),mode=0o444));t.seal();t.close();fs.close(root)
        with self.assertRaises(Denied):LiteralSource(b'bad',digest(b'abc'))

class PolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.c,cls.go,cls.identity,cls.inventory,cls.policy=sources.load()
    def raw(self):
        # New independent raw snapshot, no old fixture calls.
        G=2**30;base='/sys/fs/cgroup';path=base+'/SbfFinite-20261025-tiny-v1.scope'
        root=dict(path=base,parent=None,root=True,enabled=False,owner=base,subtree_memory=True,
          procs=[],threads=[],identities=[],type='root-special-domain',domain=base,procs_errno=0,
          controllers=['memory','pids'],pids_enabled=False,subtree_pids=True,tasks_max=None,pids_current=None)
        job=dict(path=path,parent=base,root=False,enabled=True,owner=base,subtree_memory=False,
          populated=True,procs=[17],threads=[17],identities=[dict(tid=17,tgid=17,starttime=83)],
          type='domain',domain=path,procs_errno=0,controllers=['memory','pids'],pids_enabled=True,
          subtree_pids=False,tasks_max=64,pids_current=1,current=16*2**20,cap=G,high=768*2**20,
          swap_max=0,swap_current=0,stat={k:0 for k in self.c.REQUIRED})
        return dict(rows=[root,job],self_observation=dict(pid=17,starttime=83,path=path,unified_path=path[len(base):]),
          meminfo=dict(MemTotal=96*G,MemFree=94*G-16*2**20,MemAvailable=80*G,
                       **{'Active(file)':G,'SReclaimable':2*G,'KReclaimable':3*G}))
    def old(self,s):
        a=self.c.observe(s)
        return dict(cgroups=[dict(path=p,charged_bytes=next(r['cap'] for r in s['rows'] if r['path']==p)) for p in a['frontier']],
          projected_reserved_bytes=a['bounded_reserved_bytes'],allowed=True,reserve_check=True,
          process_visibility='PID PPID RSS COMMAND CGROUP\n17 1 123 python own\n',service_visibility='',docker_visibility=[])
    def ev(self,a,b=None,old=None):
        return self.policy.evaluate(self.old(a) if old is None else old,a,a if b is None else b,0,phase='inside-scope',
          expected=dict(high=768*2**20,cap=2**30,swap_max=0,tasks_max=64),expected_unit='SbfFinite-20261025-tiny-v1.scope')
    def test_full_policy_positive_cap_once(self):
        d=self.ev(self.raw());self.assertTrue(d['allowed'],d)
        self.assertEqual(d['projected_reserved_bytes'],2**30);self.assertEqual(d['os_control_bytes'],7*2**30)
        self.assertEqual(d['safe_limit_bytes'],55*2**30)
    def test_policy_wrong_unit_cap_identity_bothscans_and_errors(self):
        for key in ('unit','cap','identity','before','after','raw','visibility','reservation','guard','reserve'):
            a=self.raw();b=copy.deepcopy(a);old=self.old(a)
            if key=='unit':a['self_observation']['unified_path']='/bad.scope'
            if key=='cap':a['rows'][1]['cap']=4*2**30
            if key=='identity':b['self_observation']['starttime']+=1
            if key=='before':a=None
            if key=='after':b=None
            if key=='raw':a['rows'][1]['stat']['anon']=-1
            if key=='visibility':old['visibility_error']='denied'
            if key=='reservation':old['projected_reserved_bytes']+=1
            if key=='guard':a['meminfo']['MemAvailable']=2*2**30
            if key=='reserve':a['meminfo']['MemAvailable']=10*2**30
            d=self.policy.evaluate(old,a,b,0,phase='inside-scope',expected=dict(high=768*2**20,cap=2**30,swap_max=0,tasks_max=64),expected_unit='SbfFinite-20261025-tiny-v1.scope')
            with self.subTest(key=key):self.assertFalse(d['allowed'],d)
    def test_adapter_bothscans_after_permission_error(self):
        # Execute the concrete adapter functions with only read-level APIs mocked.
        e=dict(os=types.SimpleNamespace(getpid=lambda:17),policy=self.policy,c=self.c,
          UNIT='SbfFinite-20261025-tiny-v1',EXPECTED=dict(high=768*2**20,cap=2**30,swap_max=0,tasks_max=64),
          subprocess=types.SimpleNamespace(SubprocessError=RuntimeError))
        calls=[];a=self.raw()
        def scan():
            calls.append('scan')
            if len(calls)==1:raise PermissionError(errno.EACCES,'synthetic')
            return a
        e.update(identity={'scan_bound':scan},visibility=lambda _:self.old(a))
        selected('SbfFiniteRss_adapter.py',['read_only_admission'],e)
        d=e['read_only_admission'](phase='inside-scope')
        self.assertEqual(calls,['scan','scan']);self.assertFalse(d['decision']['allowed']);self.assertIn('before',d['decision']['collection_failures'])

class BoundaryTests(unittest.TestCase):
    def test_public_entries_deny_before_imports(self):
        for name in ('SbfFinite_entry.py','SbfFinite_user_entry.py','SbfFinite_install_entry.py'):
            s=(H/name).read_text();t=ast.parse(s);self.assertIsInstance(t.body[0],ast.Raise)
            with self.assertRaises(SystemExit):exec(compile(t,name,'exec'),{'__name__':'__main__'})
    def test_no_full_producer_runtime_prerequisite(self):
        b=(H/'SbfFinite_backend_candidate.py').read_text();self.assertNotIn('RUNTIME_APPROVAL',b);self.assertNotIn("approval()['runtime']",b)
        self.assertIn('manifest = RUNTIME',b)
    def test_host_stdio_identity_access_extraFD(self):
        env=dict(os=os,fcntl=types.SimpleNamespace(F_GETFL=0),stat=stat,require=lambda c,r: None if c else (_ for _ in ()).throw(Denied(r)))
        # Function's fixed import uses a mock module, never ABI import/native load.
        module=types.ModuleType('SbfFiniteLinux_backend');module.inventory=lambda api:api.fds
        api=types.SimpleNamespace(fds=[0,1,2],major=lambda _:1,minor=lambda _:3,
          fstat=lambda _:types.SimpleNamespace(st_mode=stat.S_IFCHR|0o666,st_uid=0,st_rdev=0),
          flags=lambda fd:os.O_RDONLY if fd==0 else os.O_WRONLY)
        selected('SbfFinite_continue.py',['host_stdio'],env)
        with patch.dict(sys.modules,{'SbfFiniteLinux_backend':module}):
            env['host_stdio'](api)
            api.fds=[0,1,2,7]
            with self.assertRaises(Denied):env['host_stdio'](api)
            api.fds=[0,1,2];api.flags=lambda _:os.O_RDWR
            with self.assertRaises(Denied):env['host_stdio'](api)
    def test_postexec_body_identity(self):
        d=json.loads((H.parents[1]/'evidence/sbf-finite-probe-20261025/SbfFinite-renames.json').read_text())
        self.assertEqual(list(ARGV),d['captured_argv']);self.assertIn("{'SbfSeal':'tiny-public-v1'",ARGV[-1])


class LifecycleTests(unittest.TestCase):
    def env(self):
        from SbfFiniteLinux_capture import require
        return dict(require=require,Denied=Denied,os=os,time=time,errno=errno,I=lambda x:x,U=lambda x:x,
                    C=types.SimpleNamespace(c_ulong=lambda x:x),NEWNS=1,NEWNET=2,NEWPID=4)
    def test_actual_dropped_observations_reject_ids_caps_nnp_control_fd(self):
        env=self.env();ns={'mnt':1};cg=b'0::/own\n';st={'Cap'+k:'0' for k in ('Inh','Prm','Eff','Bnd','Amb')}
        st.update(NoNewPrivs='1',Threads='1');checks=[]
        env.update(status=lambda api:st,read_small=lambda *a:cg,inode=lambda s:s.key,
                   private_proc_check=lambda *a:checks.append('proc'),stdio_check=lambda *a:checks.append('stdio'))
        api=types.SimpleNamespace(getresuid=lambda:(1000,)*3,getresgid=lambda:(1000,)*3,getgroups=lambda:[],stat=lambda p:types.SimpleNamespace(key=7))
        abi=types.SimpleNamespace(prctl=lambda n:1)
        selected('SbfFinite_backend_candidate.py',['dropped_check'],env)
        env['dropped_check'](ns,cg,7,{},abi,api);self.assertEqual(checks,['proc','stdio'])
        for key,value in [('CapEff','1'),('CapBnd','1'),('NoNewPrivs','0'),('Threads','2')]:
            old=st[key];st[key]=value
            with self.subTest(key=key),self.assertRaises(Denied):env['dropped_check'](ns,cg,7,{},abi,api)
            st[key]=old
        api.getresuid=lambda:(0,1000,1000)
        with self.assertRaises(Denied):env['dropped_check'](ns,cg,7,{},abi,api)
    def test_pidfd_identity_and_parentdeath_poll_errors(self):
        env=self.env();env['read_small']=lambda *a:b'Pid:\t42\n'
        selected('SbfFinite_backend_candidate.py',['pidfd_identity','parent_alive'],env)
        env['pidfd_identity'](8,42)
        with self.assertRaises(Denied):env['pidfd_identity'](8,43)
        class Poll:
            ready=[]
            def register(self,*a):pass
            def poll(self,*a):return self.ready
        poll=Poll();env['select']=types.SimpleNamespace(poll=lambda:poll,POLLIN=1,POLLHUP=2,POLLERR=4)
        env['parent_alive'](8);poll.ready=[(8,2)]
        with self.assertRaises(Denied):env['parent_alive'](8)
    def test_owned_wait_timeout_kill_reap_permission_and_identity(self):
        for variant in ('success','timeout','permission','identity'):
            env=self.env();env['DEADLINE']=0 if variant in ('timeout','permission') else 5
            waits=[];signals=[]
            def wait(pid,flags):waits.append((pid,flags));return (43 if variant=='identity' else pid,0)
            api=types.SimpleNamespace(WNOHANG=1,waitpid=wait)
            def kill(fd):
                signals.append(fd)
                if variant=='permission':raise PermissionError(errno.EPERM,'synthetic LSM')
            abi=types.SimpleNamespace(kill_owned=kill)
            selected('SbfFinite_backend_candidate.py',['owned_wait'],env)
            if variant=='success':self.assertEqual(env['owned_wait'](42,8,abi,api),(42,0))
            else:
                with self.assertRaises((Denied,PermissionError)):env['owned_wait'](42,8,abi,api)
            if variant=='timeout':self.assertEqual(signals,[8]);self.assertEqual(waits,[(42,0)])
            if variant=='permission':self.assertEqual(signals,[8]);self.assertEqual(waits,[])
    def test_parent_backend_barrier_ownedzeroexit_and_cancel(self):
        for variant in ('ok','permission','gatewrite','controlread','nonzero'):
            env=self.env();events=[]
            class API:
                WNOHANG=1
                def getpid(self):return 9
                def pipe2(self,flags):return 20,21
                def fork(self):return 42
                def close(self,fd):events.append(('close',fd))
                def write(self,fd,b):events.append(('release',fd,b));return 0 if variant=='gatewrite' else len(b)
                def waitpid(self,pid,flags):events.append(('wait',pid));return pid,256 if variant=='nonzero' else 0
            class ABI:
                def call(self,name,pid,*a):events.append(('pidfd',pid));return 30 if pid==9 else 31
                def zero(self,*a):events.append(('unshare',))
                def check_owned_signal(self,fd):
                    events.append(('checkpermission',fd))
                    if variant=='permission':raise PermissionError(errno.EPERM,'synthetic')
                def kill_owned(self,fd):events.append(('cancel',fd))
            class Output:
                def close_writers(self):events.append(('closewriters',))
                def collect(self,waited,pid,status):
                    self_result=(waited,pid,status)
                    if waited!=pid or status!=0:raise Denied('synthetic nonzero exit')
                    events.append(('public',));return self_result
            def identity_check(fd,pid,api):
                if variant=='controlread':raise PermissionError(errno.EACCES,'synthetic fdinfo')
            env.update(root_helper_preflight=lambda api:({},b'0::/own\n',40),pidfd_identity=identity_check)
            selected('SbfFinite_backend_candidate.py',['owned_wait','internal_backend'],env);env['DEADLINE']=5
            if variant=='ok':self.assertEqual(env['internal_backend'](1,Output(),2,ABI(),API()),(42,42,0))
            else:
                with self.assertRaises((Denied,PermissionError)):env['internal_backend'](1,Output(),2,ABI(),API())
                self.assertNotIn(('public',),events)
            if variant=='ok':
                self.assertLess(events.index(('closewriters',)),events.index(('release',21,b'G')))
                self.assertLess(events.index(('wait',42)),events.index(('public',)))
            if variant in ('permission','gatewrite','controlread'):self.assertIn(('cancel',31),events)
    def test_public_capture_rejects_nonzero_wrongchild_openwriter_and_bytes(self):
        import SbfFiniteLinux_capture as cap
        for variant in ('ok','exit','identity','writer','stdout','stderr','overflow'):
            fs=FS();fs.add('/out',stat.S_IFDIR|0o700)
            good=(json.dumps({'SbfSeal':'tiny-public-v1','uid':1000,'gid':1000,'fds':[0,1,2]},sort_keys=True)+'\n').encode()
            fs.add('/out/stdout',stat.S_IFREG|0o600,b'x'*16385 if variant=='overflow' else b'bad' if variant=='stdout' else good)
            fs.add('/out/stderr',stat.S_IFREG|0o600,b'bad' if variant=='stderr' else b'')
            parent=fs.open('/out',os.O_RDONLY|os.O_DIRECTORY)
            obj=PublicOutput.__new__(PublicOutput);obj.owner=0;obj.parent=parent;obj.rows={}
            for name in ('stdout','stderr'):
                fd=fs.open(name,os.O_RDONLY,dir_fd=parent)
                obj.rows[name]=dict(r=fd,w=99 if variant=='writer' else None,inode=(1,fs.fstat(fd).st_ino))
            fs.WIFEXITED=os.WIFEXITED;fs.WEXITSTATUS=os.WEXITSTATUS;fs.SEEK_SET=os.SEEK_SET
            with patch.object(cap,'os',fs):
                if variant=='ok':self.assertEqual(obj.collect(42,42,0)['stdout'],good.decode())
                else:
                    with self.assertRaises(Denied):obj.collect(43 if variant=='identity' else 42,42,256 if variant=='exit' else 0)
    def test_guest_credentialclear_rearm_and_descriptor_barrier(self):
        # Entire concrete guest body, only individual kernel/FS calls synthetic.
        for variant in ('ok','parentdeath','drop','fd','exec'):
            env=self.env();events=[]
            class Exit(BaseException):pass
            class API:
                def fstat(self,fd):return types.SimpleNamespace(key=7)
                def fchdir(self,fd):events.append('fchdir')
                def chroot(self,s):events.append('chroot')
                def chdir(self,s):pass
                def close(self,fd):events.append(('close',fd))
                def dup2(self,a,b,inheritable):events.append(('dup2',a,b))
                def execve(self,path,argv,env):
                    events.append(('exec',path,tuple(argv),env))
                    raise Exit() if variant=='ok' else OSError(errno.EPERM,'synthetic exec')
                def _exit(self,code):events.append(('exit',code));raise Exit()
            class ABI:
                def prctl(self,*a):events.append(('pdeath',)+a);return 0
                def mount_id(self,fd):return 5
                def zero(self,*a):events.append(('zero',)+a)
                def guest_limits(self):events.append('limits')
                def drop(self,cap):
                    events.append('drop')
                    if variant=='drop':raise PermissionError(errno.EPERM,'synthetic')
                def close_escape_fds(self):events.append('closeescape')
            calls=[]
            def alive(fd):
                calls.append(fd)
                if variant=='parentdeath' and len(calls)==2:raise Denied('synthetic dead parent')
            env.update(parent_alive=alive,child_namespaces=lambda *a:{},private_propagation=lambda *a:None,
              capture_runtime=lambda *a:None,mount_guest=lambda *a:(6,{'root':5}),inode=lambda s:s.key,
              stdio_install=lambda *a:{},private_proc_check=lambda *a:None,
              inventory=lambda *a:[0,1,2,3,99] if variant=='fd' else [0,1,2,3],
              dropped_check=lambda *a:events.append('droppedcheck'),FIXED_PROBE=ARGV,ENV=RUNTIME['env'])
            selected('SbfFinite_backend_candidate.py',['guest'],env)
            with self.assertRaises(Exit):env['guest'](1,None,2,{},b'cg',40,ABI(),API(),RUNTIME,8)
            if variant=='ok':
                # API exec raises synthetic control exception then guest cleanup:
                # execution is only an event, never a native effect.
                self.assertEqual(calls,[8,3]);self.assertEqual(events.count(('pdeath',1,9)),2)
                self.assertLess(events.index('drop'),max(i for i,e in enumerate(events) if e==('pdeath',1,9)))
                self.assertIn(('exec',ARGV[0],ARGV,RUNTIME['env']),events)
            if variant in ('drop','fd','parentdeath'):self.assertFalse(any(isinstance(e,tuple) and e[0]=='exec' for e in events))

class AdditionalPolicyTests(unittest.TestCase):
    def test_root_preflight_capability_control_namespace_and_cgroup_checks(self):
        from SbfFiniteLinux_capture import require
        needed=sum(1<<n for n in (5,6,7,8,18,21))
        for variant in ('ok','uid','gid','caps','threads','nnp','seccomp','caplast','cgroup'):
            st=dict(Threads='1',NoNewPrivs='0',Seccomp='0',CapEff=hex(needed))
            if variant=='caps':st['CapEff']='0'
            if variant=='threads':st['Threads']='2'
            if variant=='nnp':st['NoNewPrivs']='1'
            if variant=='seccomp':st['Seccomp']='2'
            def read(path,api,bound):
                if path.endswith('cap_last_cap'):return b'41\n' if variant=='caplast' else b'40\n'
                return b'1:legacy\n' if variant=='cgroup' else b'0::/finite\n'
            env=dict(os=os,require=require,status=lambda api:st,read_small=read,namespaces=lambda api:{'mnt':3})
            selected('SbfFinite_backend_candidate.py',['root_helper_preflight'],env)
            api=types.SimpleNamespace(getresuid=lambda:(1,0,0) if variant=='uid' else (0,0,0),getresgid=lambda:(1,0,0) if variant=='gid' else (0,0,0))
            if variant=='ok':self.assertEqual(env['root_helper_preflight'](api),({'mnt':3},b'0::/finite\n',40))
            else:
                with self.subTest(variant=variant),self.assertRaises(Denied):env['root_helper_preflight'](api)
    def test_guard_real_sample_owned_descendant_permission_cancel_and_budget(self):
        # Import contains definitions only; no thread/native/metadata call.
        from SbfFiniteRss_guard import Guard,GuardError,BUDGET
        class Proc:
            large=False
            def optional(self,pid):return dict(pid=pid,ppid=0 if pid==1 else 1,starttime=pid+10,rss_bytes=BUDGET if self.large else 100)
            def children(self,pid):return {2} if pid==1 else set()
            def cancel(self,pid,start):raise PermissionError(errno.EPERM,'synthetic root descendant')
        p=Proc();g=Guard(proc=p,pid=1,notify=lambda:None);g.sample()
        self.assertEqual(g.peak,200);self.assertEqual(set(g.owned),{1,2})
        g.cancel_owned();self.assertIn('cancellation-error',g.cancelled[0]['outcome'])
        p.large=True
        with self.assertRaises(GuardError):g.sample()
    def test_actual_control_parser_rejects_pressure_swap_wrongcap_and_unreadable(self):
        import SbfFinite_observe as observe
        # Imports adapter definitions and sealed pure policy only; no calls.
        expected=observe.EXPECTED
        v={'memory.high':str(expected['high']),'memory.max':str(expected['cap']),
           'memory.swap.max':'0','memory.swap.current':'0','pids.max':'64',
           'memory.peak':'10','memory.current':'10','pids.current':'1',
           'memory.events':'high 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'}
        self.assertTrue(observe.check_controls(dict(values=v)))
        for k,x in [('memory.high','1'),('memory.max',str(4*2**30)),('memory.swap.current','1'),
                    ('memory.events',v['memory.events'].replace('oom 0','oom 1')),('memory.current',{'errno':13}),('pids.current','65')]:
            with self.subTest(key=k),self.assertRaises(ValueError):observe.check_controls(dict(values=dict(v,**{k:x})))

class SourceInventoryTests(unittest.TestCase):
    def test_package_literal_payload_external_bootstrap_and_disabled_sources(self):
        import SbfFinite_inventory as inventory
        import SbfFinite_package_pins as package_pins
        import SbfFinite_launcher_pin as launcher
        rows=inventory.PACKAGE_CATALOG
        self.assertEqual(len({r['name'] for r in rows}),len(rows))
        for r in rows:
            self.assertEqual(r['payload'],(H/r['name']).read_bytes())
            self.assertEqual({k:r['pin'][k] for k in ('size','sha256')},digest(r['payload']))
            self.assertEqual(r['pin']['mode'],0o444)
            if r['name'].endswith('.py'):
                t=ast.parse(r['payload']);self.assertIsInstance(t.body[0],(ast.If,ast.Raise))
                if isinstance(t.body[0],ast.If):
                    self.assertEqual(ast.unparse(t.body[0].test),"__name__ == '__main__'")
                    self.assertIsInstance(t.body[0].body[0],ast.Raise)
        self.assertNotIn('SbfFinite_package_pins.py',package_pins.FILES)
        self.assertEqual(set(package_pins.FILES)|{'SbfFinite_package_pins.py','SbfFinite_entry.py','SbfFinite_user_entry.py'},{r['name'] for r in rows})
        self.assertEqual(launcher.LAUNCHER_PIN,digest((H/'SbfFinite_root_launcher.sh.txt').read_bytes()))
        self.assertLess(sum(r['pin']['size'] for r in rows),2**20)
    def test_all_catalog_chains_are_complete_and_exact_to_canonical_endpoint(self):
        # Reconstruct only literal captured metadata in memory. Never touches the
        # captured host paths or opens an actual runtime source file.
        for r in CATALOG:
            fs=FS()
            for c in r['source']['chain']:
                ident=c['identity'];p=c['path']
                node=types.SimpleNamespace(st_dev=ident[0],st_ino=ident[1],st_mode=ident[2],st_uid=ident[3],st_gid=ident[4],
                  st_nlink=ident[5],st_size=ident[6],st_mtime_ns=ident[7],st_ctime_ns=ident[8],data=b'',target=c.get('target'))
                fs.nodes[p]=node
            s=Source(r['source'],fs);s.audit();s.close()
            self.assertEqual(fs.handles,{})
    def test_fixed_installer_retains_partial_layout_without_delete_or_adoption(self):
        t=ast.parse((H/'SbfFinite_install.py').read_text())
        forbidden={'unlink','rmdir','rename','replace','chown','link','symlink','execve','system','Popen'}
        self.assertEqual({n.attr for n in ast.walk(t) if isinstance(n,ast.Attribute)}&forbidden,set())
        f=next(n for n in t.body if isinstance(n,ast.FunctionDef) and n.name=='fixed_install')
        self.assertEqual(f.args.args,[]);self.assertEqual(f.args.kwonlyargs,[])
        self.assertIn('O_EXCL',(H/'SbfFinite_install.py').read_text())

class InstallerInventoryTests(unittest.TestCase):
    def test_unknown_extra_entry_and_new_inode_bad_rights_are_rejected(self):
        fs,row=setup();root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY);t=Tree(root,fs)
        s=Source(row,fs);t.copy(s,'/a',dict(digest(b'abc'),mode=0o444));s.close()
        fs.add('/dest/unreviewed',stat.S_IFREG|0o600,b'x')
        with self.assertRaises(Denied):t.seal()
        self.assertEqual(stat.S_IMODE(fs.nodes['/dest/a'].st_mode),0o600)
        t.close();fs.close(root)
        for key,value in [('st_uid',1000),('st_gid',1000),('st_nlink',2),('st_mode',stat.S_IFIFO|0o600)]:
            fs,row=setup();root=fs.open('/dest',os.O_RDONLY|os.O_DIRECTORY);t=Tree(root,fs);s=Source(row,fs)
            oldopen=fs.open
            def badopen(path,flags,mode=0o777,dir_fd=None):
                fd=oldopen(path,flags,mode,dir_fd)
                if flags&os.O_CREAT:setattr(fs.handles[fd]['node'],key,value)
                return fd
            fs.open=badopen
            with self.subTest(key=key),self.assertRaises(Denied):t.copy(s,'/a',dict(digest(b'abc'),mode=0o444))
            self.assertFalse(t.writers);t.close();s.close();fs.close(root)

class DormantLoaderTests(unittest.TestCase):
    def env(self):
        import importlib.abc,importlib.util
        fs=FS();fs.add('/sealed',stat.S_IFDIR|0o555);fs.add('/sealed/a.py',stat.S_IFREG|0o444,b'value=7\n')
        for key in ('O_RDONLY','O_DIRECTORY','O_NOFOLLOW','O_CLOEXEC','O_NONBLOCK'):setattr(fs,key,getattr(os,key))
        pins={'a.py':digest(b'value=7\n')}
        env=dict(os=fs,stat=stat,hashlib=hashlib,importlib=importlib,SbfFinite_ROOT='/sealed',SbfFinite_PINS=pins)
        selected('SbfFinite_entry.py',['SbfFinite_require','SbfFinite_identity','SbfFinite_read','SbfFinite_loader'],env)
        return env,fs
    def test_concrete_sealed_reader_hash_size_chain_writer_alias_and_drift(self):
        for variant in ('ok','uid','gid','writable','hardlink','symlink','ancestry','hash','size','growth','entryrace','path'):
            e,fs=self.env();pin=e['SbfFinite_PINS']['a.py'];n=fs.nodes['/sealed/a.py'];name='a.py'
            if variant=='uid':n.st_uid=1000
            if variant=='gid':n.st_gid=1000
            if variant=='writable':n.st_mode=stat.S_IFREG|0o644
            if variant=='hardlink':n.st_nlink=2
            if variant=='symlink':n.st_mode=stat.S_IFLNK|0o777
            if variant=='ancestry':fs.nodes['/sealed'].st_mode|=0o002
            if variant=='hash':n.data=b'value=8\n'
            if variant=='size':n.st_size+=1
            if variant=='growth':n.data+=b'x'
            if variant=='path':name='../a.py'
            if variant=='entryrace':
                def mutate(api,fd):
                    if api.handles[fd]['path']=='/sealed/a.py':api.add('/sealed/a.py',stat.S_IFREG|0o444,b'value=7\n')
                fs.onread=mutate
            if variant=='ok':self.assertEqual(e['SbfFinite_read'](name,pin),b'value=7\n')
            else:
                with self.subTest(variant=variant),self.assertRaises((RuntimeError,OSError)):e['SbfFinite_read'](name,pin)
            self.assertEqual(fs.handles,{})
    def test_concrete_importer_unknown_prefix_and_tiny_ast_execution(self):
        e,fs=self.env();loader=e['SbfFinite_loader']({'SbfFiniteTiny.py':b'value=7\n'})
        self.assertIsNone(loader.find_spec('os'))
        self.assertIsNotNone(loader.find_spec('SbfFiniteTiny'))
        with self.assertRaises(RuntimeError):loader.find_spec('SbfFiniteUnlisted')
        m=types.ModuleType('SbfFiniteTiny');loader.exec_module(m);self.assertEqual(m.value,7)
        self.assertEqual(m.__file__,'/sealed/SbfFiniteTiny.py')
    def test_noargument_main_env_preloaded_bounds_and_complete_pinmaps(self):
        # Dormant main executes against isolated synthetic sys/import surfaces,
        # not the real import machinery or any operational module.
        for variant in ('ok','argv','env','preloaded','bounds'):
            e,fs=self.env();fake=types.SimpleNamespace(argv=['/sealed/SbfFinite_entry.py'],modules={},meta_path=[])
            fs.environ={'HOME':'/probe','LC_ALL':'C','PATH':'/usr/bin','TMPDIR':'/tmp'}
            e.update(sys=fake,SbfFinite_ENV=dict(fs.environ),SbfFinite_MODULE='SbfFinite_continue',SbfFinite_FUNCTION='root_continuation')
            calls=[]
            e['__import__']=lambda n: (calls.append(n) or types.SimpleNamespace(root_continuation=lambda:0))
            if variant=='argv':fake.argv.append('userpath')
            if variant=='env':fs.environ['PYTHONPATH']='/untrusted'
            if variant=='preloaded':fake.modules['SbfFinite_untrusted']=object()
            if variant=='bounds':e['SbfFinite_PINS']={}
            selected('SbfFinite_entry.py',['SbfFinite_main'],e)
            if variant=='ok':self.assertEqual(e['SbfFinite_main'](),0);self.assertEqual(calls,['SbfFinite_continue'])
            else:
                with self.assertRaises(RuntimeError):e['SbfFinite_main']()
                self.assertEqual(calls,[])
            self.assertEqual(fake.meta_path,[])
        # Installed entries pin core+package-pins but never themselves. Installer
        # pins its full fixed bootstrap input catalog; no hash fixed point.
        for name in ('SbfFinite_entry.py','SbfFinite_user_entry.py','SbfFinite_install_entry.py'):
            tree=ast.parse((H/name).read_text());values={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)}
            self.assertNotIn(name,values['SbfFinite_PINS'])
            for source,pin in values['SbfFinite_PINS'].items():self.assertEqual(pin,digest((H/source).read_bytes()))
            self.assertEqual(values['SbfFinite_FUNCTION'],{'SbfFinite_entry.py':'root_continuation','SbfFinite_user_entry.py':'user_producer','SbfFinite_install_entry.py':'fixed_install_entry'}[name])

class InstallerEntryRepairTests(unittest.TestCase):
    def run_entry(self,variant='ok'):
        # Entire actual installer functions/classes and dormant entry/main/bottom.
        # All OS calls hit FS; imports resolve only explicit synthetic modules.
        import importlib.abc,importlib.util,gc
        gc.collect() # release previous synthetic OS/function cycles before next case
        from SbfFiniteLinux_capture import require,canonical,DIR_FLAGS,FILE_FLAGS
        fs=FS()
        for k in ('O_WRONLY','O_CREAT','O_EXCL','O_NOFOLLOW','O_CLOEXEC'):
            setattr(fs,k,getattr(os,k))
        fs.getresuid=fs.getresgid=lambda:(0,0,0)
        for p in ('/var','/var/lib','/opt','/opt/aspis','/src'):
            fs.add(p,stat.S_IFDIR|0o755)
        catalog=[];payloads={}
        # Exercise all actual 92 copy iterations / exact original byte accounting
        # with new synthetic bytes, not host/captured source access.
        for i in range(92):
            size=387560 if i<91 else 35655597-91*387560
            path='/src/f'+str(i)
            if size not in payloads:payloads[size]=b'x'*size
            data=payloads[size]
            fs.add(path,stat.S_IFREG|0o444,data)
            chain=[dict(path=p,identity=list(identity(fs.nodes[p]))) for p in ('/','/src',path)]
            catalog.append(dict(guest='/f'+str(i),mode=0o444,
                source=dict(path=path,physical=path,size=size,sha256=digest(data)['sha256'],chain=chain)))
        original_stat=fs.stat
        def stat_call(path,dir_fd=None,follow_symlinks=False):
            if variant=='entrydrift' and path=='installation-source-outcome.json':
                fs.add(receipt_path,stat.S_IFREG|0o600,b'replacement retained')
            try:return original_stat(path,dir_fd,follow_symlinks)
            except KeyError:raise FileNotFoundError(path)
        fs.stat=stat_call
        original_write=fs.write;original_chmod=fs.fchmod;original_fsync=fs.fsync
        receipt_path='/var/lib/SbfFinite-20261025-v1/journal-root/installation-source-outcome.json'
        def write(fd,b):
            p=fs.handles[fd]['path']
            if variant=='copy' and p.endswith('/rootfs/f0'):raise OSError('synthetic copy failure')
            if variant=='receiptwrite' and p==receipt_path:raise OSError('synthetic receipt write failure')
            return original_write(fd,b)
        fs.write=write
        def chmod(fd,mode):
            if variant=='seal':raise OSError('synthetic seal failure')
            return original_chmod(fd,mode)
        fs.fchmod=chmod
        def sync(fd):
            if variant=='receiptfsync' and fs.handles[fd]['path']==receipt_path:raise OSError('synthetic receipt fsync failure')
            if variant=='dirfsync' and fs.handles[fd]['path'].endswith('/journal-root'):raise OSError('synthetic journal fsync failure')
            original_fsync(fd)
        fs.fsync=sync
        oldopen=fs.open
        def open_call(path,flags,mode=0o777,dir_fd=None):
            if variant in ('existingreceipt','symlinkreceipt') and path=='installation-source-outcome.json' and flags&os.O_CREAT:
                fs.add(receipt_path,stat.S_IFLNK|0o777 if variant=='symlinkreceipt' else stat.S_IFREG|0o600,b'old retained',target='/never-follow')
            fd=oldopen(path,flags,mode,dir_fd)
            if fs.handles[fd]['path']==receipt_path and flags&os.O_CREAT:
                node=fs.handles[fd]['node']
                if variant=='uid':node.st_uid=1000
                if variant=='gid':node.st_gid=1000
                if variant=='nlink':node.st_nlink=2
                if variant=='mode':node.st_mode=stat.S_IFREG|0o644
            return fd
        fs.open=open_call
        modules={
            'SbfFinite_continue':types.SimpleNamespace(host_stdio=lambda:None),
            'SbfFinite_backend_candidate':types.SimpleNamespace(status=lambda:{'Threads':'1'}),
            'SbfFinite_inventory':types.SimpleNamespace(PACKAGE_CATALOG=[]),
            'SbfFinite_validate':types.SimpleNamespace(validate_fixed=lambda:None)}
        imports=[]
        def imp(name,*args,**kwargs):imports.append(name);return modules[name]
        e=dict(os=fs,stat=stat,time=time,hashlib=hashlib,require=require,identity=identity,
            canonical=canonical,DIR_FLAGS=DIR_FLAGS,FILE_FLAGS=FILE_FLAGS,CATALOG=catalog,
            OWN='/var/lib/SbfFinite-20261025-v1',__import__=imp)
        t=ast.parse((H/'SbfFinite_install.py').read_text())
        nodes=[n for n in t.body if isinstance(n,(ast.FunctionDef,ast.ClassDef,ast.Assign))]
        # Import statements inside functions use explicit builtins import mock.
        e['__builtins__']=dict(vars(__import__('builtins')),__import__=imp)
        exec(compile(ast.Module(body=nodes,type_ignores=[]),'actual-installer-under-OS-mocks','exec'),e)
        modules['SbfFinite_install']=types.SimpleNamespace(fixed_install_entry=e['fixed_install_entry'])
        entry=ast.parse((H/'SbfFinite_install_entry.py').read_text())
        vals={n.targets[0].id:ast.literal_eval(n.value) for n in entry.body if isinstance(n,ast.Assign)}
        fs.environ=dict(vals['SbfFinite_ENV'])
        fake=types.SimpleNamespace(argv=[vals['SbfFinite_ROOT']+'/SbfFinite_install_entry.py'],modules={},meta_path=[])
        reads=[]
        def read(name,pin):
            self.assertEqual(digest((H/name).read_bytes()),pin);reads.append(name);return b'# synthetic transport only\n'
        v=dict(vals,os=fs,sys=fake,stat=stat,hashlib=hashlib,importlib=importlib,
               SbfFinite_read=read,__builtins__=dict(vars(__import__('builtins')),__import__=imp),__name__='__main__')
        selected('SbfFinite_install_entry.py',['SbfFinite_require','SbfFinite_loader','SbfFinite_main'],v)
        def invoke():
            try:exec(compile(ast.Module(body=[entry.body[-1]],type_ignores=[]),'actual-entry-bottom','exec'),v)
            finally:self.assertEqual(fake.meta_path,[])
        if variant=='ok':
            with self.assertRaises(SystemExit) as raised:invoke()
            self.assertIs(type(raised.exception.code),int);self.assertEqual(raised.exception.code,0)
            self.assertEqual(fs.nodes[receipt_path].data,e['INSTALL_RECEIPT'])
            self.assertLessEqual(len(fs.nodes[receipt_path].data),512)
            self.assertEqual(stat.S_IMODE(fs.nodes[receipt_path].st_mode),0o600)
            self.assertEqual((fs.nodes[receipt_path].st_uid,fs.nodes[receipt_path].st_gid), (0,0))
            writes=[x for x in fs.events if x[0]=='open' and x[1]==receipt_path and x[3]&os.O_CREAT]
            self.assertEqual(len(writes),1)
            events=list(fs.events)
            with self.assertRaises(RuntimeError):invoke() # existing installation, never adopt/retry
            self.assertEqual(fs.nodes[receipt_path].data,e['INSTALL_RECEIPT'])
            self.assertEqual(len([x for x in fs.events if x[0]=='open' and x[1]==receipt_path and x[3]&os.O_CREAT]),1)
            self.assertIn(('fsync',writes[0][2]),events)
        else:
            with self.assertRaises((OSError,Denied)):invoke()
            if variant in ('copy','seal'):self.assertNotIn(receipt_path,fs.nodes)
            else:
                self.assertIn(receipt_path,fs.nodes) # partial/full failed publication retained
                self.assertEqual(stat.S_IMODE(fs.nodes['/var/lib/SbfFinite-20261025-v1/rootfs/f0'].st_mode),0o444)
            self.assertIn('/var/lib/SbfFinite-20261025-v1/rootfs/f0',fs.nodes)
        self.assertEqual(fs.handles,{})
        self.assertEqual(imports.count('SbfFinite_install'),2 if variant=='ok' else 1)
        self.assertEqual(len(reads),len(vals['SbfFinite_PINS'])*(2 if variant=='ok' else 1))
    def test_actual_dormant_installer_success_integer_zero_fixed_receipt_once(self):self.run_entry()
    def test_actual_copy_and_seal_failures_do_not_publish_success(self):
        for variant in ('copy','seal'):
            with self.subTest(variant=variant):self.run_entry(variant)
    def test_actual_receipt_write_sync_and_rights_errors_retain_copy(self):
        for variant in ('receiptwrite','receiptfsync','dirfsync','uid','gid','nlink','mode','entrydrift','existingreceipt','symlinkreceipt'):
            with self.subTest(variant=variant):self.run_entry(variant)

    def test_wrapper_rejects_nonexact_result_and_entry_contracts_are_unchanged(self):
        from SbfFiniteLinux_capture import require
        for result in (None,0,{},dict(status='wrong',rows=92,bytes=35655597)):
            calls=[]
            def install():calls.append('install');return result
            e=dict(fixed_install=install,require=require)
            selected('SbfFinite_install.py',['fixed_install_entry'],e)
            with self.assertRaises(Denied):e['fixed_install_entry']()
            self.assertEqual(calls,['install'])
        # Every dormant entry uses the identical shared noargument main and
        # SystemExit bottom. Only installer function changed; no integer coercion
        # imposed on root/user continuation functions.
        template=ast.parse((H/'SbfFinite_sealed_entry.py.template.txt').read_text()
            .replace('@ROOT@',"'/placeholder'").replace('@PINS@','{}')
            .replace('@MODULE@',"'placeholder'").replace('@FUNCTION@',"'placeholder'")
            .replace('@ENTRY@',"'placeholder'"))
        for name,function in [('SbfFinite_entry.py','root_continuation'),('SbfFinite_user_entry.py','user_producer')]:
            tree=ast.parse((H/name).read_text())
            vals={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign)}
            self.assertEqual(vals['SbfFinite_FUNCTION'],function)
            self.assertEqual(ast.dump(tree.body[-1]),ast.dump(template.body[-1]))
            self.assertIsInstance(tree.body[0],ast.Raise)
        install=ast.parse((H/'SbfFinite_install.py').read_text())
        wrapper=next(n for n in install.body if isinstance(n,ast.FunctionDef) and n.name=='fixed_install_entry')
        self.assertEqual(ast.unparse(wrapper.returns),'int')
        self.assertEqual(wrapper.args.args,[]);self.assertEqual(wrapper.args.kwonlyargs,[])
