#!/usr/bin/env python3
"""Synthetic metadata tests only: no Cargo, compiler or host process inspection."""
import hashlib,importlib.util,json,pathlib,resource,tempfile,time,sys,subprocess
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';start=time.monotonic()
s=importlib.util.spec_from_file_location('proc',T/'SbfCachePrep_proc.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
checks=[]
def check(name,ok):
    checks.append(dict(name=name,passed=bool(ok)));assert ok,name

def fixture(root,kernel=False,threads=1):
    d=root/'42';d.mkdir();(d/'fd').mkdir();(d/'fdinfo').mkdir()
    # stat fields 3..22: state, ppid..flags at9, starttime at22.
    tail=['S']+['0']*19;tail[6]=str(0x200000 if kernel else 0);tail[19]='1234'
    (d/'stat').write_text('42 (name with ) spaces) '+' '.join(tail))
    (d/'status').write_text(f'State:\tS\nTgid:\t42\nPid:\t42\nPPid:\t1\nUid:\t0 0 0 0\nGid:\t0 0 0 0\nThreads:\t{threads}\n')
    (d/'cmdline').write_bytes(b'' if kernel else b'ordinary\0');(d/'cgroup').write_text('0::/synthetic\n')
    if not kernel:
        (d/'cwd').symlink_to('/');(d/'exe').symlink_to('/usr/bin/python3')
    return d
check('stat parser handles comm parentheses',m.identity('42 (a ) b) '+' '.join(['S']+['0']*18+['99']))['starttime']==99)
for kind in ('ordinary','kernel','threads','missing','donor-cwd','donor-fd','pid-change'):
    with tempfile.TemporaryDirectory(prefix='SbfCachePrep-') as tmp:
        root=pathlib.Path(tmp);d=fixture(root,kind=='kernel',2 if kind=='threads' else 1)
        if kind=='missing':(d/'exe').unlink()
        if kind=='donor-cwd':(d/'cwd').unlink();(d/'cwd').symlink_to(m.ROOTS[0])
        if kind=='donor-fd':
            (d/'fd'/'7').symlink_to(m.ROOTS[1]+'/deps/foo (deleted)');(d/'fdinfo'/'7').write_text('flags:\t0100002\n')
        r=m.observe(root)
        check(kind+' admission',r['allowed_to_enter']==(kind in ('ordinary','kernel','pid-change')))
        if kind=='kernel':check('kernel explicit classification',r['processes'][0]['classification']=='kernel-thread')
        if kind=='pid-change':
            original=m.identity;calls=[0]
            def changed(raw):
                out=original(raw);calls[0]+=1
                if calls[0]%2==0:out['starttime']+=1
                return out
            m.identity=changed;check('PID reuse denied',not m.observe(root)['allowed_to_enter']);m.identity=original
check('unknown path is not membership',not m.member('/unrelated/private'))
u=resource.getrusage(0)
r=dict(checks=checks,receipt=dict(command=[sys.executable,'-B',str(T/'SbfCachePrep_test.py')],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),print_axioms='N/A'),dependencies={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (T/'SbfCachePrep_proc.py',pathlib.Path(__file__))})
(E/'synthetic-proc-tests.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
