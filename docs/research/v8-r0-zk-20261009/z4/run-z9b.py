#!/usr/bin/env python3
"""Build/run the optimized Z9b computation and preserve evidence. Adapted from
run-z9.py. One probe process per (structure, vector, query set); both gamma
limb sets are evaluated inside each process. `--summarize DIR` re-parses only.
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, shutil, subprocess, time
p=argparse.ArgumentParser();p.add_argument('--out');p.add_argument('--preflight',action='store_true');p.add_argument('--jobs',type=int,default=5)
p.add_argument('--revision',default='unknown');p.add_argument('--summarize');p.add_argument('--random',type=int,default=200);p.add_argument('--worst',type=int,default=20);p.add_argument('--only');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3]
def kv(text):
    out={}
    for k,x in re.findall(r'(\w+)=(\[[^\]]*\]|[^\s\[]+)',text):
        try:out[k]=json.loads(x)
        except Exception:out[k]=x
    return out
def jobs():
    js=[(s,v,'actual') for s in ('A','J') for v in range(5)]
    js+=[('A',0,q) for q in ('consecutive0','spaced','paired')]
    js+=[('A' if k%2==0 else 'J',k%5,f'random:{k}') for k in range(args.random)]
    js+=[('A' if k%2==0 else 'J',k%5,f'{m}:{k}') for m in ('consecutive','coset') for k in range(args.worst)]
    return js
def name(s,v,q):return f"probe-{s}-{v}-{q.replace(':','_')}"
def parse(d):
    out=[]
    for f in sorted(d.glob('probe-*.log')):
        r={'file':f.name,'lines':{}}
        for line in f.read_text().splitlines():
            tag=line.split(' ')[0]
            if tag.startswith('Z9B_') or tag in ('STOP',) or tag.startswith('Z9_EXPLAIN'):
                d2=kv(line);key=tag+('|'+str(d2.get('gamma')) if 'gamma' in d2 else '')+('|lane'+str(d2.get('lane')) if tag=='Z9B_C1LIFT' else '')
                r['lines'][key]=d2
        out.append(r)
    return out
def table(rows):
    agg={'jobs':len(rows),'c1lift_fail_jobs':[],'h1lift_fail_jobs':[],'bcondg_fail':[],'b0own_le_vg_fail':[],'unexplained_nonzero':[],'geometry_mismatch':[],'weights_mismatch':[]}
    for r in rows:
        L=r['lines'];f=r['file']
        li=L.get('Z9B_LIFTS',{})
        if li.get('c1lift_all') is not True:agg['c1lift_fail_jobs'].append((f,li.get('c1lift_failing_lanes')))
        if li.get('h1lift') is not True:agg['h1lift_fail_jobs'].append(f)
        g=L.get('Z9B_GEOMETRY',{})
        if any(g.get(k)!=0 for k in ('x18_vs_rust_levels0_mismatch','natural_eval_vs_rust_mismatch','x16_basis_vs_rust_accumulate_mismatch')):agg['geometry_mismatch'].append(f)
        for gi in (0,1):
            b=L.get(f'Z9B_BCOND|{gi}',{});dz=L.get(f'Z9B_DESIGN|{gi}',{})
            if not b:agg['bcondg_fail'].append((f,gi,'missing'));continue
            if b.get('BCondG_R1_per_reading',[None,None])[1] is not True:agg['bcondg_fail'].append((f,gi,b.get('BCondG_R1_per_reading')))
            if b.get('B0own_le_V_G') is not True:agg['b0own_le_vg_fail'].append((f,gi))
            if b.get('unexplained_annihilator')!=0:agg['unexplained_nonzero'].append((f,gi))
            if dz.get('weightsR1_equals_rust_materialize') is not True:agg['weights_mismatch'].append((f,gi))
    return agg
if args.summarize:
    d=pathlib.Path(args.summarize).resolve();rows=parse(d);agg=table(rows)
    (d/'summary.json').write_text(json.dumps({'aggregate':agg,'jobs':rows},indent=1)+'\n');print(json.dumps(agg,indent=1));raise SystemExit(0)
out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(n):
    try:return (cg/n).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0'}:raise SystemExit('Requires MemoryHigh=3G, MemoryMax=4G, MemorySwapMax=0')
manifest={}
files=[root/'Cargo.toml',here/'Cargo.toml',here/'Cargo.lock',here/'probe.rs',here/'probe-C.log',here/'run-z9b.py']+sorted(here.glob('z*.rs'))
for crate in ['aspis-core','aspis-statement','aspis-prover']:
    files.extend(sorted((root/'crates'/crate/'src').rglob('*.rs')));files.append(root/'crates'/crate/'Cargo.toml')
for f in files:manifest[str(f.relative_to(root))]=hashlib.sha256(f.read_bytes()).hexdigest()
cargo=shutil.which('cargo') or str(pathlib.Path.home()/'.cargo/bin/cargo');receipts=[]
def run(cmd,label):
    start=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=root)
        _,status,ru=os.wait4(proc.pid,0);rc=os.waitstatus_to_exitcode(status)
    rec=dict(target=label,command=cmd,source_revision=args.revision,exit_status=rc,wall_seconds=time.monotonic()-start,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=read('memory.peak'),cgroup_swap_peak=read('memory.swap.peak'))
    receipts.append(rec);print(json.dumps(rec),flush=True);return rc
def evidence(status):
    (out/'evidence.json').write_text(json.dumps(dict(source_revision=args.revision,rustc=subprocess.check_output([str(pathlib.Path(cargo).with_name('rustc')),'--version'],text=True).strip(),caps=caps,scope=str(cg),mode='z9b',preflight=args.preflight,concurrency=args.jobs,source_sha256=manifest,receipts=receipts,exit_status=status,axioms_audit='Not applicable: no Lean executed'),indent=2)+'\n')
binary=str(here/'target/release/probe')
def job(s,v,q):return run([binary,'--z9b','--structure',s,'--vector',str(v),'--qset',q],name(s,v,q))
status=run([cargo,'build','--release','--locked','--offline','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
if status!=0:evidence(status);raise SystemExit(status)
js=[('A',0,'actual'),('A',0,'consecutive0')] if args.preflight else ([(l.split(',')[0],int(l.split(',')[1]),l.split(',')[2]) for l in pathlib.Path(args.only).read_text().split()] if args.only else jobs())
with concurrent.futures.ThreadPoolExecutor(1 if args.preflight else args.jobs) as ex:codes=list(ex.map(lambda x:job(*x),js))
status=0 if all(c==0 for c in codes) else 1
rows=parse(out);agg=table(rows);(out/'summary.json').write_text(json.dumps({'aggregate':agg,'jobs':rows},indent=1)+'\n');print(json.dumps(agg,indent=1))
evidence(status);raise SystemExit(status)
