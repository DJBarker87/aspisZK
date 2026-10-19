#!/usr/bin/env python3
"""One small local Lean target using existing objects; never build dependencies."""
from pathlib import Path
import argparse,hashlib,json,os,re,resource,signal,subprocess,sys,time
ap=argparse.ArgumentParser();ap.add_argument('module');ap.add_argument('attempt');a=ap.parse_args()
repo=Path(__file__).resolve().parents[5];area=repo/'docs/research/100bit-spend-path-20261013'
source=area/'lean'/(a.module+'.lean');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert '#print axioms' in source.read_text()
assert not re.search(r'\b(sorry|admit|axiom)\b',source.read_text().replace('#print axioms',''))
private=repo/'.cu-local-proof';private.mkdir(exist_ok=True)
(private/'.gitignore').write_text('*\n')
(private/'lakefile.toml').write_text('name = "CuSavingsLocal"\nversion = "0.1.0"\n')
(private/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
objects=private/'objects';objects.mkdir(exist_ok=True)
cache=Path('/Users/dominic/ZK/AspisFormal/.lake/packages')
paths=[objects,*sorted(p for p in cache.glob('*/.lake/build/lib/lean') if p.is_dir())]
imports={}
for module in re.findall(r'^import ([A-Za-z0-9_\.]+)\s*$',source.read_text(),re.M):
    if module=='Lean':continue
    candidates=[p/(module.replace('.','/')+'.olean') for p in paths]
    found=next((p for p in candidates if p.exists()),None)
    assert found is not None,('Missing cached direct import; do not cold-build',module)
    imports[module]=dict(path=str(found),sha256=sha(found))
out=area/'evidence/cu-equivalence-20261019'/a.attempt;out.mkdir(exist_ok=False)
(out/'source.lean').write_bytes(source.read_bytes())
object_path=objects/(a.module+'.olean');object_path.parent.mkdir(parents=True,exist_ok=True)
command=['/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','env',
    'LEAN_PATH='+':'.join(map(str,paths)),'lean','--root='+str(area/'lean'),'-M7000',
    '-o',str(object_path),str(source)]
revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
plan=dict(command=command,cwd=str(private),module=a.module,attempt=a.attempt,
    source_revision=revision,source_sha256=sha(source),features=['pool-adapter','private-leaf-salts'],
    imports=imports,resource_scope='focused_local',
    resource_limit_method='Lean -M7000 plus aggregate descendant RSS monitor stopping at 7 GiB; no dependency build',
    expected_work='One small changed theorem using existing mathlib objects; no generated certificate aggregation')
(out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
started=time.monotonic();peak=0;stopped=False
before=resource.getrusage(resource.RUSAGE_CHILDREN)
with (out/'stdout.log').open('w') as stdout,(out/'stderr.log').open('w') as stderr:
    proc=subprocess.Popen(['/usr/bin/time','-l','-o',str(out/'time.log'),*command],cwd=private,
        stdout=stdout,stderr=stderr,start_new_session=True)
    while proc.poll() is None:
        rows=subprocess.check_output(['ps','-eo','pid,ppid,rss'],text=True).splitlines()[1:]
        entries=[tuple(map(int,r.split())) for r in rows if len(r.split())==3]
        descendants={proc.pid};previous=set()
        while previous!=descendants:
            previous=set(descendants)
            descendants.update(pid for pid,parent,_ in entries if parent in descendants)
        rss=sum(rss*1024 for pid,_,rss in entries if pid in descendants);peak=max(peak,rss)
        if rss>=7*2**30 or time.monotonic()-started>600:
            os.killpg(proc.pid,signal.SIGTERM);stopped=True
            try:proc.wait(timeout=3)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL)
            break
        time.sleep(.2)
    status=proc.wait()
usage=resource.getrusage(resource.RUSAGE_CHILDREN);timing=(out/'time.log').read_text()
match=re.search(r'(\d+)\s+maximum resident set size',timing)
peak_bytes=int(match[1]) if match else usage.ru_maxrss
stdout=(out/'stdout.log').read_text();stderr=(out/'stderr.log').read_text()
receipt=dict(plan,exit_status=status,wall_seconds=time.monotonic()-started,
    peak_rss_kib=(peak_bytes+1023)//1024,peak_aggregate_rss_bytes_sampled=peak,
    process_swaps=usage.ru_nswap-before.ru_nswap,cgroup_swap_bytes=None,
    stopped_for_limit=stopped,print_axioms_output=stdout+stderr,
    object_sha256=sha(object_path) if status==0 else None,
    mathlib_revision=subprocess.check_output(['git','-C',str(cache/'mathlib'),'rev-parse','HEAD'],text=True).strip())
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(stdout);print(stderr);print(json.dumps({k:receipt[k] for k in
    ['exit_status','wall_seconds','peak_rss_kib','peak_aggregate_rss_bytes_sampled','process_swaps']}))
raise SystemExit(status)
