#!/usr/bin/env python3
"""Build/run only the optimized Z8c balanced-mask-space computation and preserve source/evidence.

Adapted from run-z8b.py. Each (structure, vector) job is its own probe process
inside this one capped scope; receipts are recorded per process. Structures
A, B, I, J (Z8) and K, L, M (design §3.3 (8)). A silent rank below 1,076 is a
finding, not a stop. `--summarize DIR` re-parses an existing output directory only.
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time
p=argparse.ArgumentParser();p.add_argument('--out');p.add_argument('--preflight',action='store_true');p.add_argument('--vectors',type=int,default=5);p.add_argument('--jobs',type=int,default=5);p.add_argument('--structures',default='A,B,I,J,K,L,M');p.add_argument('--summarize');args=p.parse_args()
here=pathlib.Path(__file__).resolve().parent;root=here.parents[3]
STRUCTS=args.structures.split(',')

def kv(text):
    out={}
    for k,x in re.findall(r'(\w+)=(\[[^\]]*\]|\[\[.*?\]\]|[^\s\[]+)',text):
        try:out[k]=json.loads(x)
        except Exception:out[k]=x
    return out

def parse(log_dir, vectors):
    ref={}
    for line in (here/'probe-C.log').read_text().splitlines():
        m=re.match(r'(CHALLENGE trial=(\d+) .*)',line)
        if m:ref[('c',int(m.group(2)))]=line
        m=re.match(r'Z4B_REPLAY trial=(\d+) pair=(\d+) (.*)',line)
        if m:ref[('t',int(m.group(1)),int(m.group(2)))]=m.group(3)
    out={'structures':{}}
    for s in STRUCTS:
        recs=[]
        for v in range(vectors):
            f=log_dir/f'probe-{s}-{v}.log'
            if not f.exists():continue
            r={'vector':v,'results':{},'lines':{},'lanes':{},'replay_challenge_match':None,'replay_terminal_match':None}
            terms=[]
            for line in f.read_text().splitlines():
                tag=line.split(' ')[0]
                if line.startswith('CHALLENGE '):r['replay_challenge_match']=(line==ref.get(('c',v)))
                elif tag=='Z8C_RANKS':
                    kind=re.search(r'kind=(\S+)',line).group(1);d={}
                    for k in ['total','round_full','round_limb']:
                        m=re.search(k+r'=(\[\[.*?\]\]|\[.*?\]|\d+)',line)
                        if m:d[k]=json.loads(m.group(1))
                    r['lines']['RANKS:'+kind]=d
                elif line.startswith('RESULT '):
                    m=re.match(r'RESULT structure=\S+ vector=\d+ (\S+) image_rank=(\d+) targets=(\d+) failures=(\d+) excess_rank=(\d+) quotient_support=(\[.*?\]) excess_pivots=(\[.*?\])$',line)
                    sup=re.findall(r'"([^"]*)"',m.group(6));piv=re.findall(r'"([^"]*)"',m.group(7))
                    r['results'][m.group(1)]=dict(image_rank=int(m.group(2)),targets=int(m.group(3)),failures=int(m.group(4)),excess_rank=int(m.group(5)),support_size=len(sup),support=sup,excess_pivots=piv)
                elif tag in ('Z8C_LANE_OWN','Z8C_LANE_OT','Z8C_F5','Z8C_LANE_OTPRIME'):
                    lane=re.search(r'lane=(\S+)',line).group(1)
                    r['lanes'].setdefault(lane,{})[tag]=line.split(f'lane={lane} ')[1]
                elif tag in ('Z8C_LEFT_KERNEL','Z8C_LEFT_KERNEL_REST_UNION'):
                    kind=re.search(r'kind=(\S+)',line).group(1)
                    r['lines'][tag+':'+kind]=line.split(f'kind={kind} ')[1]
                elif tag=='Z8C_LEFT_KERNEL_REST':
                    r['lines'].setdefault('LEFT_KERNEL_REST',[]).append(line.split('vector=')[1][2:])
                elif tag=='Z8C_ALPHA':
                    m=re.search(r'alpha=(\[.*?\]\]) lambda_dims=(\[.*?\]) good3=(\w+) outside_k2=(\[.*?\])',line)
                    r['alpha_limbs']=json.loads(m.group(1));r['lambda_dims']=json.loads(m.group(2));r['good3']=m.group(3)=='true';r['outside_k2']=json.loads(m.group(4))
                elif tag=='Z8C_OPENING':
                    r['opening_limbs']={k:json.loads(x) for k,x in re.findall(r'(gamma|kappa|tau|fold)=(\[.*?\])',line)}
                elif tag=='Z8C_TERMINAL':
                    m=re.search(r'pair=(\d+) (.*)',line);terms.append((int(m.group(1)),m.group(2)))
                elif tag.startswith('Z8C_') or tag=='STOP':
                    body=line.split('vector=',1)[1][2:] if 'vector=' in line else line
                    r['lines'][tag]=kv(body) if tag not in ('Z8C_B',) else body
                    if tag in ('Z8C_DONE','Z8C_PREFLIGHT_DONE'):r['wall_seconds']=float(line.split('wall_seconds=')[1])
            if s=='A' and terms:r['replay_terminal_match']=all(ref.get(('t',v,pr))==x for pr,x in terms) and len(terms)==5
            recs.append(r)
        if recs:out['structures'][s]=recs
    return out

def table(summary):
    lines=[]
    for s,recs in summary['structures'].items():
        for r in recs:
            g=r['lines'].get('Z8C_GATE',{});pu=r['lines'].get('Z8C_GATE_PURE',{})
            lines.append(f"{s} v{r['vector']} silent={pu.get('silent_rank')} retained={pu.get('initial_retained_rank')} batched={pu.get('batched_pivots')} i={g.get('i_pass')} ii={g.get('ii_pass')} wall={r.get('wall_seconds')}")
    return '\n'.join(lines)

if args.summarize:
    d=pathlib.Path(args.summarize).resolve();s=parse(d,args.vectors)
    (d/'summary.json').write_text(json.dumps(s,indent=1)+'\n');print(table(s));raise SystemExit(0)

out=pathlib.Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[-1].lstrip('/')
def read(name):
    try:return (cg/name).read_text().strip()
    except FileNotFoundError:return None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
if caps!={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0'}:raise SystemExit('Requires explicit MemoryHigh, MemoryMax and MemorySwapMax=0')
manifest={}
files=[root/'Cargo.toml',here/'Cargo.toml',here/'Cargo.lock',here/'probe.rs',here/'z5.rs',here/'z6.rs',here/'z7.rs',here/'z8.rs',here/'z8b.rs',here/'z8c.rs',here/'run-z8c.py',here/'probe-C.log']
for crate in ['aspis-core','aspis-statement','aspis-prover']:
    files.extend((root/'crates'/crate/'src').rglob('*.rs'));files.append(root/'crates'/crate/'Cargo.toml')
    if (root/'crates'/crate/'build.rs').exists():files.append(root/'crates'/crate/'build.rs')
for f in files:
    if not f.exists():raise SystemExit(f'Missing source: {f}')
    rel=f.relative_to(root);manifest[str(rel)]=hashlib.sha256(f.read_bytes()).hexdigest();dest=out/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dest)
cargo=shutil.which('cargo') or str(pathlib.Path.home()/'.cargo/bin/cargo');receipts=[]
def run(cmd,label):
    start=time.monotonic()
    with (out/f'{label}.log').open('w') as log:
        proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,cwd=root)
        _,status,ru=os.wait4(proc.pid,0);proc.returncode=os.waitstatus_to_exitcode(status)
    receipt=dict(target=label,command=cmd,exit_status=proc.returncode,wall_seconds=time.monotonic()-start,peak_child_rss_kib=ru.ru_maxrss,swaps=ru.ru_nswap,cgroup_memory_peak=read('memory.peak'),cgroup_swap_peak=read('memory.swap.peak'))
    receipts.append(receipt);print(json.dumps(receipt),flush=True);return proc.returncode
def evidence(status,stop=None):
    (out/'evidence.json').write_text(json.dumps(dict(base_revision='054164c8c',rustc=subprocess.check_output([str(pathlib.Path(cargo).with_name('rustc')),'--version'],text=True).strip(),caps=caps,source_sha256=manifest,receipts=receipts,scope=str(cg),mode='z8c',preflight=args.preflight,structures=STRUCTS,vectors=args.vectors,concurrency=args.jobs,stop=stop,exit_status=status,axioms_audit='Not applicable: no Lean executed'),indent=2)+'\n')
binary=str(here/'target/release/probe')
def job(s,v,extra=()):return run([binary,'--z8c','--structure',s,'--vector',str(v),*extra],f'probe-{s}-{v}')
start=time.monotonic()
status=run([cargo,'build','--release','--locked','--manifest-path',str(here/'Cargo.toml'),'-j2'],'compile')
if status!=0:evidence(status,'compile');raise SystemExit(status)
if args.preflight:
    status=job('A',0,['--preflight']);evidence(status);raise SystemExit(status)
jobs_list=[(s,v) for s in STRUCTS for v in range(args.vectors)]
with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
    codes=list(ex.map(lambda sv:job(*sv),jobs_list))
status=0 if all(c==0 for c in codes) else 1
with (out/'probe-Z8c.log').open('w') as log:
    for s in STRUCTS:
        for v in range(args.vectors):
            f=out/f'probe-{s}-{v}.log'
            if f.exists():log.write(f.read_text())
summary=parse(out,args.vectors);summary['total_probe_wall_seconds']=time.monotonic()-start
(out/'summary.json').write_text(json.dumps(summary,indent=1)+'\n');print(table(summary))
evidence(status);raise SystemExit(status)
