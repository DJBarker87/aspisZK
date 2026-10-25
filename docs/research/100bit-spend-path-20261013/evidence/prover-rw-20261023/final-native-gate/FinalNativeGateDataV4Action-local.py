"""Single allocated invocation; exclusive records prevent replay. No remote fallback."""
import ast,base64,datetime,hashlib,json,os,pathlib,resource,shutil,subprocess,sys,tempfile,time
E=pathlib.Path(__file__).resolve().parent
R=pathlib.Path.cwd()
T=R/'tools/prover-rw-20261023/final-native-gate/prospective-data-v4'
P='FinalNativeGateDataV4Action-'
def write(name,obj):
    with (E/(P+name)).open('x') as f:json.dump(obj,f,indent=2,sort_keys=True);f.write('\n');f.flush();os.fsync(f.fileno())
def pin(p):
    b=p.read_bytes();return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def git(*args):return subprocess.check_output(['git',*args],text=True).strip()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def preflight():
    start=time.monotonic();ident=json.loads((T/'FinalNativeGate-release-identities.json').read_text())
    for name,key in [('FinalNativeGate-data-transfer.py','receiver'),('FinalNativeGate-data-transport.py','transport')]:assert pin(T/name)==ident[key]
    tree=ast.parse((T/'FinalNativeGate-data-transfer.py').read_bytes())
    rows=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='FILES' for x in n.targets))
    manifest={};decoded={}
    for name,row in rows.items():
        b=base64.b85decode(row['b85']);assert len(b)==row['size'] and hashlib.sha256(b).hexdigest()==row['sha256']
        manifest[name]={'size':len(b),'sha256':row['sha256']};decoded[name]=b
    assert manifest==ident['transfer_manifest'] and len(rows)==46
    root=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest();assert root==ident['transfer_manifest_root']
    plan=json.loads(decoded['FinalNativeGate-plan.json']);bootstrap=json.loads(decoded['FinalNativeGate-bootstrap.json'])
    for name,row in bootstrap.items():assert manifest[name]==row
    assert decoded['FinalNativeGate_seal.py']==('PLAN_SHA256 = '+repr(manifest['FinalNativeGate-plan.json']['sha256'])+'\n').encode()
    lead=pathlib.Path('/private/tmp/lead-final-native-v4-review-20261025-v1/receipt.json')
    assert json.loads(lead.read_text())['status']=='PASS_V4_SOURCE_RELEASE_REPRODUCTION'
    write('preflight.json',dict(utc=utc(),exit=0,wall_seconds=time.monotonic()-start,source_revision=git('rev-parse','HEAD'),maintained_source='3e4b5df592',plan_source_revision=plan['source_revision'],plan_job_revision=plan['job_revision'],receiver=pin(T/'FinalNativeGate-data-transfer.py'),transport=pin(T/'FinalNativeGate-data-transport.py'),release_identities=pin(T/'FinalNativeGate-release-identities.json'),transfer_manifest=manifest,transfer_root=root,lead_review_reused=dict(path=str(lead),**pin(lead)),python=dict(executable=sys.executable,realpath=os.path.realpath(sys.executable),pin=pin(pathlib.Path(sys.executable)),version=sys.version),argv=['python3','-B',str(T.relative_to(R)/'FinalNativeGate-data-transport.py')],peak_self_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A raw DATA; no theorem',remote_absence='UNOBSERVED; exclusive receiver rejects all existing entries',admission='remote reviewed prospective full scan BEFORE scope; actual inside and GO scans BEFORE acquisition/publish; no separate SSH'))
def sample(root):
    todo=[root];seen=set();total=0;rows=[]
    while todo:
        pid=todo.pop()
        if pid in seen:continue
        seen.add(pid)
        p=subprocess.run(['/bin/ps','-p',str(pid),'-o','pid=,ppid=,rss='],capture_output=True,text=True)
        for line in p.stdout.splitlines():
            v=list(map(int,line.split()));rows.append(v);total+=v[2]*1024
        p=subprocess.run(['/usr/bin/pgrep','-P',str(pid)],capture_output=True,text=True)
        todo.extend(int(v) for v in p.stdout.split())
    return dict(elapsed=time.monotonic(),rss_bytes=total,processes=rows)
def run():
    pre=json.loads((E/(P+'preflight.json')).read_text())
    assert pin(T/'FinalNativeGate-data-transfer.py')==pre['receiver'] and pin(T/'FinalNativeGate-data-transport.py')==pre['transport']
    argv=['python3','-B',str(T.relative_to(R)/'FinalNativeGate-data-transport.py')]
    packet=pathlib.Path(tempfile.mkdtemp(prefix=P,dir='/private/tmp'));os.chmod(packet,0o700)
    write('launch.json',dict(utc=utc(),argv=argv,source_revision=git('rev-parse','HEAD'),private_capture=str(packet),main_actions_charged=1,conditional_actions_charged=0,print_axioms='N/A'))
    start=time.monotonic();samples=[]
    with (packet/'stdout').open('xb') as out,(packet/'stderr').open('xb') as err:
        child=subprocess.Popen(argv,stdout=out,stderr=err,cwd=R)
        while child.poll() is None:
            s=sample(os.getpid());s['elapsed']-=start;samples.append(s)
            if s['rss_bytes']>=512*2**20:
                # Resolve the owned transport and its direct SSH child; never abandon.
                for pid,ppid,rss in reversed(s['processes']):
                    if pid!=os.getpid():
                        try:os.kill(pid,15)
                        except ProcessLookupError:pass
            time.sleep(.05)
        rc=child.wait()
    u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
    write('execution.json',dict(utc_end=utc(),argv=argv,pid=child.pid,exit=rc,wall_seconds=time.monotonic()-start,peak_self_rss_bytes=u.ru_maxrss,peak_serial_child_rss_bytes=c.ru_maxrss,sampled_aggregate_peak_bytes=max(s['rss_bytes'] for s in samples),swap_self=u.ru_nswap,swap_children=c.ru_nswap,samples=samples,private_capture=str(packet),source_revision=git('rev-parse','HEAD'),print_axioms='N/A'))
    for name in ('stdout','stderr'):
        with (E/(P+'transport.'+name)).open('xb') as f:f.write((packet/name).read_bytes())
    print(json.dumps(dict(exit=rc,packet=str(packet))))
if __name__=='__main__':
    {'preflight':preflight,'run':run}[sys.argv[1]]()
