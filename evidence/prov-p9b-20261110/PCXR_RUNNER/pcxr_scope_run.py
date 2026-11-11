#!/usr/bin/env python3
"""PCXR_ runs INSIDE one admitted scope (MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64): one lean process, one module.
argv[1] = job json written by the runner. Writes receipt json. Shape copied from L187_runner.py / S2W_run_host.py."""
import hashlib,json,os,pathlib,re,subprocess,sys,time
job=json.loads(pathlib.Path(sys.argv[1]).read_text());rcp=pathlib.Path(job['receipt'])
rel=pathlib.Path('/sys/fs/cgroup')/next(l.split(':',2)[2].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
limits={n:(rel/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},limits
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
src=pathlib.Path(job['src']);ssha=sha(src)
row=dict(module=job['module'],target=job['target'],source=str(src),source_sha256=ssha,expected_source_sha256=job.get('expected_source_sha256'),
  import_key=job['import_key'],imports=job['imports'],source_revision=job['source_revision'],limits=limits,argv=None,cgroup=str(rel),lean_path=job['lean_path'])
if job.get('expected_source_sha256') and ssha!=job['expected_source_sha256']:
    row.update(exit=97,status='FAIL_SOURCE_MISMATCH');rcp.write_text(json.dumps(row,indent=1));sys.exit(97)
tmpdir=pathlib.Path(job['tmpdir']);tmpdir.mkdir(parents=True,exist_ok=True)
tmp=tmpdir/(job['unit']+'.olean');tf=tmpdir/(job['unit']+'.time')
cmd=[job['lean'],'-j1','-M7000','-DElab.async=false','-R',job['root'],'-o',str(tmp),str(src)]
env=dict(PATH='/usr/bin:/bin',LEAN_SYSROOT=job['sysroot'],LEAN_PATH=job['lean_path'],TMPDIR=str(tmpdir))
t0=time.monotonic()
r=subprocess.run(['/usr/bin/time','-v','-o',str(tf),'timeout','180',*cmd],cwd=job['cwd'],env=env,capture_output=True,text=True)
wall=time.monotonic()-t0;tt=tf.read_text() if tf.exists() else ''
log=r.stdout+r.stderr
m=lambda n:next((l.split(':',1)[1].strip() for l in tt.splitlines() if n in l),None)
row.update(argv=cmd,exit=r.returncode,status='PASS' if r.returncode==0 else 'FAIL',wall_seconds=round(wall,3),peak_rss_kib=m('Maximum resident set size'),swaps=m('Swaps'),
  cgroup_memory_peak_bytes=(rel/'memory.peak').read_text().strip(),sorry_warnings=len(re.findall(r"declaration uses '?sorry'?",log)),
  axioms_lines=[l for l in log.splitlines() if 'axioms' in l][:60],timed_out=(r.returncode==124),diagnostics_tail=log[-2500:])
out=pathlib.Path(job['out_olean'])
if r.returncode==0 and tmp.is_file():
    out.parent.mkdir(parents=True,exist_ok=True);moved=[]
    for sib in sorted(tmpdir.glob(tmp.name+'*')):
        dest=pathlib.Path(str(out)+sib.name[len(tmp.name):]);os.replace(sib,dest);moved.append(dest.name)
    for ext in ['.ir','.ilean','.c']:
        sib=tmp.with_suffix(ext)
        if sib.is_file():dest=out.with_suffix(ext);os.replace(sib,dest);moved.append(dest.name)
    row.update(olean_sha256=sha(out),object_files=moved)
    l187=pathlib.Path(job['l187_obj']) if job.get('l187_obj') else None
    if l187 and l187.is_file():row['olean_identical_to_l187']=(sha(l187)==row['olean_sha256'])
else:
    for sib in list(tmpdir.glob(tmp.name+'*'))+[tmp.with_suffix(e) for e in ['.ir','.ilean','.c']]:
        if sib.is_file():sib.unlink()
tf.unlink(missing_ok=True)
rcp.write_text(json.dumps(row,indent=1));print(json.dumps({k:row.get(k) for k in('module','status','exit','wall_seconds','peak_rss_kib','swaps')}))
sys.exit(r.returncode)
