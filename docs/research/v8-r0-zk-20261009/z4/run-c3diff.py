#!/usr/bin/env python3
"""Z9d (D49.4 C3) differential test: build optimized, run emit + z9c check + the
extraction-friendly checker (c3/check) once per configuration, sequentially,
with per-process receipts."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--revision',default='unknown');p.add_argument('--preflight',action='store_true');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3];out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(n):
    try:return (cg/n).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}:raise SystemExit('Requires MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0')
manifest={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [here/'probe.rs',here/'z9.rs',here/'z9b.rs',here/'z9c.rs',here/'z9d.rs',here/'z5.rs',here/'Cargo.toml',here/'Cargo.lock',here/'run-c3diff.py',here.parent/'c3/check/src/lib.rs',here.parent/'c3/check/Cargo.toml',here.parent/'c3/build/src/lib.rs',here.parent/'c3/build/Cargo.toml']}
cargo=shutil.which('cargo') or str(pathlib.Path.home()/'.cargo/bin/cargo');receipts=[]
def run(cmd,label):
    start=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=root);_,status,ru=os.wait4(proc.pid,0);rc=os.waitstatus_to_exitcode(status)
    rec=dict(target=label,command=cmd,source_revision=args.revision,exit_status=rc,wall_seconds=time.monotonic()-start,user_seconds=ru.ru_utime,system_seconds=ru.ru_stime,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=read('memory.peak'),cgroup_swap_peak=read('memory.swap.peak'))
    receipts.append(rec);print(json.dumps(rec),flush=True);return rc
st=run([cargo,'build','--release','--offline','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
b=str(here/'target/release/probe')
cfgs=[('A',0,'actual',0,True)] if args.preflight else [('A',0,'actual',0,True),('A',0,'actual',1,False),('J',1,'actual',0,False),('A',3,'random:0',1,False),('A',2,'coset:0',0,False),('B',0,'actual',0,False)]
codes=[]
if st==0:
    for s,v,q,g,teeth in cfgs:codes.append(run([b,'--r1cert','--c3diff','--structure',s,'--vector',str(v),'--qset',q,'--gamma',str(g)]+(['--teeth'] if teeth else []),f'c3diff-{s}-{v}-{q.replace(":","_")}-g{g}'))
status=0 if st==0 and all(c==0 for c in codes) else 1
(out/'evidence.json').write_text(json.dumps(dict(source_revision=args.revision,caps=caps,scope=str(cg),cpu=subprocess.check_output(['sh','-c','lscpu | grep "Model name"'],text=True).strip(),source_sha256=manifest,receipts=receipts,exit_status=status),indent=2)+'\n')
raise SystemExit(status)
