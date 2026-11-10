import json,re,os,sys,hashlib,subprocess,collections
S=sys.argv[1]; ROOT=sys.argv[2]+"/evidence"  # plan_map, evidence root
plan=json.load(open(S))
H64=re.compile(r'^[0-9a-f]{64}$')
PATH=re.compile(r'((?:docs/research/100bit-spend-path-20261013/)?(?:evidence|lean|lean-candidates)/[\w./+-]*?([A-Za-z0-9_]+)\.lean)')
cites=collections.defaultdict(lambda: collections.defaultdict(set))  # module -> (kind,value)->jobs
IDX=collections.defaultdict(list)
for l in open(sys.argv[3]).read().split('\n'):
    if l: IDX[l.rsplit('/',1)[-1]].append(l)
def norm(p):
    m=re.search(r'(?:evidence|lean|lean-candidates)/.*$',p); tail=m.group(0) if m else p
    c=[x for x in IDX.get(p.rsplit('/',1)[-1],[]) if x.endswith('/'+tail) or x==tail]
    if len(c)>=1: return sorted(c,key=len)[0]
    return 'UNRESOLVED:'+p
def norm_old(p): 
    p=p.strip()
    return p if p.startswith('docs/') else 'docs/research/100bit-spend-path-20261013/'+p
def job_of(f): return f.split('/')[0]
def addpath(mod,p,job,f):
    if '/prov-' in p or p.startswith('prov-') or 'evidence/prov-' in p: return
    cites[mod][('path',norm(p))].add(job+'|'+f)
def walk(o,job,f):
    if isinstance(o,dict):
        mod=o.get('module')
        if isinstance(mod,str) and mod in plan:
            for k,v in o.items():
                if isinstance(v,str) and H64.match(v) and k in('blob','sha256','sha','source_sha256','source_sha'):
                    cites[mod][('sha',v)].add(job+'|'+f)
        for v in o.values(): walk(v,job,f)
    elif isinstance(o,list):
        for v in o: walk(v,job,f)
    elif isinstance(o,str):
        for m in PATH.finditer(o):
            if m.group(2) in plan: addpath(m.group(2),m.group(1),job,f)
n=0
for d in sorted(os.listdir(ROOT)):
    if not d.startswith('prov-p') or d.startswith('prov-p5h'): continue
    dd=os.path.join(ROOT,d)
    for dp,_,fs in os.walk(dd):
        for fn in fs:
            f=os.path.join(dp,fn)
            if os.path.getsize(f)>40_000_000 or not (fn.endswith(('.json','.md','.py','.sh','.txt','.jsonl')) or (fn.startswith('gate_') and fn.endswith('.lean'))): continue
            try: t=open(f,errors='ignore').read()
            except: continue
            n+=1
            rel=os.path.relpath(f,ROOT)
            if fn.endswith('.json'):
                try: walk(json.loads(t),d,rel)
                except Exception: pass
            for m in PATH.finditer(t):
                if m.group(2) in plan: addpath(m.group(2),m.group(1),d,rel)
            for m in re.finditer(r'\bsha(?:256)?[ =:"\']{1,3}([0-9a-f]{8})(?![0-9a-f])',t):
                lo=max(0,m.start()-200)
                for mm in re.finditer(r'[A-Za-z0-9_]+',t[lo:m.start()+20]):
                    pass
            # gate_<Module>.lean input copies
            if fn.startswith('gate_') and fn.endswith('.lean'):
                mod=fn[5:-5]
                if mod in plan:
                    cites[mod][('input_copy_sha',hashlib.sha256(open(f,'rb').read()).hexdigest())].add(d+'|'+rel)
# resolve cited paths to sha via git
paths=sorted({v for m in cites for (k,v) in cites[m] if k=='path'})
shaof={}
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,cwd=ROOT)
for q in paths:
    if q.startswith('UNRESOLVED'): shaof[q]=None; continue
    p.stdin.write(('research:%s\n'%q).encode()); p.stdin.flush()
    hdr=p.stdout.readline().decode().split()
    if len(hdr)==3 and not q.startswith('UNRESOLVED'):
        sz=int(hdr[2]); data=p.stdout.read(sz); p.stdout.read(1); shaof[q]=hashlib.sha256(data).hexdigest()
    else: shaof[q]=None
p.stdin.close()
out=[]
samesha=[]
for mod in sorted(cites):
    pp,ps,lab=plan[mod]
    for (k,v),jobs in sorted(cites[mod].items(),key=lambda x:x[0]):
        if k=='path':
            sh=shaof.get(v)
            if v.startswith('UNRESOLVED:'): sh=None
            diff=(sh!=ps)
            if v!=pp and sh==ps: samesha.append((mod,v))
            if diff: out.append(dict(module=mod,cited_path=v,cited_sha256=sh,cited_sha_note=None if sh else 'path not found on research',plan_path=pp,plan_sha256=ps,plan_label=lab,kind='path_cite',jobs=sorted({j.split('|')[0] for j in jobs}),files=sorted({j.split('|')[1] for j in jobs})[:6]))
        elif k=='sha':
            if v!=ps: out.append(dict(module=mod,cited_path=None,cited_sha256=v,plan_path=pp,plan_sha256=ps,plan_label=lab,kind='sha_cite',jobs=sorted({j.split('|')[0] for j in jobs}),files=sorted({j.split('|')[1] for j in jobs})[:6]))
        else:
            if v!=ps: out.append(dict(module=mod,cited_path=sorted(jobs)[0].split('|')[1],cited_sha256=v,plan_path=pp,plan_sha256=ps,plan_label=lab,kind='generator_input_copy_sha',jobs=sorted({j.split('|')[0] for j in jobs}),files=sorted({j.split('|')[1] for j in jobs})[:6]))
json.dump(dict(same_sha_other_path=len(samesha),files_scanned=n,modules_cited=len(cites),differences=out),open('PCWR_SOURCE_SHA_AUDIT_raw.json','w'),indent=1)
print(n,len(cites),len(out),collections.Counter(o['kind'] for o in out))
