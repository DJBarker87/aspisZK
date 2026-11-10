import json,glob,re,os,subprocess,collections,sys
sys.dont_write_bytecode=True
fc=json.load(open('/tmp/pcxl_classes.json'))['final_class']
man={m['module']:m for m in json.load(open('replay-l187-20261109/L187_SOURCE_MANIFEST.json'))['modules']}
excl=('RPu_FIq_Native','AspisR1Post25Sampler.Funs','RPz7_WAdm_Fissioned','S8OwnedP6','OraclePortCkptAbi2','S1ValuesOwnedModelV1','AspisR1Qm31SamplerIndex','AdapterRwModel','NCV_','NCX_','NEG_','NGD_','NJS_Extract.Funs','AspisR1TerminalDecoder.Funs','AspisR1DecodeKFullV10.Funs','NGT_Emitted')
def find_gate(m):
    p=((man.get(m) or {}).get('recovered') or {}).get('chosen_source_path')
    if p:
        b=subprocess.run(['git','-C','/Users/dominic/ZK','show','research:'+p],capture_output=True).stdout.decode('utf8','replace')
        if b: return b,p
    fn='gate_'+m.replace('.','_')+'.lean'
    g=sorted(glob.glob('*/inputs/'+fn))
    if g: return open(g[-1]).read(),g[-1]
    return None,None
SPLIT=r'\n(?=(?:/--|@\[|def |theorem |abbrev |instance |structure |inductive |variable |end |namespace |axiom |opaque |impl_def ))'
def name(p):
    m=re.search(r'(?:^|\n)(?:@\[[^\]]*\]\s*)*(?:partial_fixpoint\s+)?(def|abbrev|instance|structure|inductive|impl_def)\s+(?:\{[^}]*\}\s*)?([\w.]+)',p); return m.group(2) if m else None
def decls(t): return {name(p):p for p in re.split(SPLIT,t) if name(p)}
def norm(s,ns,gns): return re.sub(r'\s+','',re.sub(r'/--.*?-/','',s,flags=re.S).replace(ns,gns))
ops=collections.defaultdict(list)
for k,v in fc.items():
    if v=='OPEN' and not k.startswith(excl): ops[k.split('|')[0]].append(k.split('|')[1])
efiles=[f for f in glob.glob('*/*_emitted/raw/*/Funs.lean')+glob.glob('*/*/raw/*/Funs.lean')+glob.glob('*/*_emitted/raw/*/Types.lean') if 'prov-p5i' not in f]
cache={}
out={}
for m,ds in sorted(ops.items(),key=lambda x:-len(x[1])):
    gt,gp=find_gate(m)
    if gt is None: out[m]=dict(n=len(ds),gate=None); continue
    gns=(re.findall(r'(?m)^namespace\s+(\S+)',gt) or [''])[0]
    gd=decls(gt)
    shorts={d:(d[len(gns)+1:] if d.startswith(gns+'.') else d) for d in ds}
    best=None
    for f in efiles:
        if f not in cache:
            t=open(f).read(); cache[f]=(decls(t),(re.findall(r'(?m)^namespace\s+(\S+)',t) or [''])[0])
        fd,fns=cache[f]
        ident=[];diff=[]
        for d,s in shorts.items():
            if s in fd and s in gd:
                (ident if norm(fd[s],fns,gns)==norm(gd[s],gns,gns) else diff).append(s)
        if ident and (best is None or len(ident)>len(best[1])): best=(f,ident,diff)
    out[m]=dict(n=len(ds),gate=gp,best=(best[0],len(best[1]),best[2][:3]) if best else None)
json.dump(out,open('prov-p5i-20261110/PCWS_reuse_scan.json','w'),indent=1)
for m,v in out.items():
    if v.get('best'): print(v['n'],m,v['best'][1],v['best'][0].split('/raw/')[0])
print('no gate:',[m for m,v in out.items() if v['gate'] is None][:40])
