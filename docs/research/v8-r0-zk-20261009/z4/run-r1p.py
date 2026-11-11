#!/usr/bin/env python3
"""R1-P cost measurement: build optimized, run the P_R1 prototype once per
configuration, sequentially (concurrency 1), with per-process receipts."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--revision',default='unknown');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3];out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(n):
    try:return (cg/n).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0'}:raise SystemExit('Requires MemoryHigh=3G, MemoryMax=4G, MemorySwapMax=0')
manifest={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [here/'probe.rs',here/'z9.rs',here/'z9b.rs',here/'z5.rs',here/'Cargo.toml',here/'Cargo.lock',here/'run-r1p.py']}
cargo=shutil.which('cargo') or str(pathlib.Path.home()/'.cargo/bin/cargo');receipts=[]
def run(cmd,label):
    start=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=root);_,status,ru=os.wait4(proc.pid,0);rc=os.waitstatus_to_exitcode(status)
    rec=dict(target=label,command=cmd,source_revision=args.revision,exit_status=rc,wall_seconds=time.monotonic()-start,user_seconds=ru.ru_utime,system_seconds=ru.ru_stime,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=read('memory.peak'),cgroup_swap_peak=read('memory.swap.peak'))
    receipts.append(rec);print(json.dumps(rec),flush=True);return rc
st=run([cargo,'build','--release','--locked','--offline','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
b=str(here/'target/release/probe')
cfgs=[('A',0,'actual',0),('A',0,'actual',1),('J',1,'actual',0),('A',2,'coset:0',0),('A',3,'random:0',1),('A',0,'consecutive0',0)]
codes=[]
if st==0:
    for s,v,q,g in cfgs:codes.append(run([b,'--r1p','--structure',s,'--vector',str(v),'--qset',q,'--gamma',str(g)],f'r1p-{s}-{v}-{q.replace(":","_")}-g{g}'))
    codes.append(run(['taskset','-c','0',b,'--r1p','--structure','A','--vector','0','--qset','actual','--gamma','0'],'r1p-A-0-actual-g0-onecore'))
status=0 if st==0 and all(c==0 for c in codes) else 1
(out/'evidence.json').write_text(json.dumps(dict(source_revision=args.revision,caps=caps,scope=str(cg),cpu=subprocess.check_output(['sh','-c','lscpu | grep "Model name"'],text=True).strip(),source_sha256=manifest,receipts=receipts,exit_status=status),indent=2)+'\n')
raise SystemExit(status)
