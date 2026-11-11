#!/usr/bin/env python3
"""PCXR_: compute the PIN2 rebuild set (transitive importers of changed modules), layers and estimate.
Inputs: L187 plan (read from host, copy sha recorded), L187 per-module receipts (research evidence), overlay listing,
W2 impact TSV. Pure computation, no host access."""
import json,glob,lzma,os,sys,collections,hashlib,heapq,statistics
E=os.path.dirname(os.path.abspath(__file__))
L187=os.path.join(E,'..','replay-l187-20261109')
plan=json.load(open(E+'/L187_PLAN_READ.json'))['plan']
imps={m:[i for i in v['imports'] if i in plan] for m,v in plan.items()}
rev=collections.defaultdict(list)
for m,l in imps.items():
    for i in l: rev[i].append(m)
# L187 per-module receipts
rc={}
for f in sorted(glob.glob(L187+'/batches/*/results.jsonl.xz')):
    for l in lzma.open(f,'rt'):
        r=json.loads(l)
        if r.get('exit')==0 and r.get('wall_seconds') is not None:
            rc[r['module']]=(float(r['wall_seconds']),int(r.get('peak_rss_kib') or 0))
assert set(rc)==set(plan),(len(rc),len(plan))
overlay=sorted(json.load(open(E+'/PCXR_OVERLAY_LISTING.json'))['modules'])
ov_in=[m for m in overlay if m in plan]
ov_out=[m for m in overlay if m not in plan]
impact=sorted({l.split('\t')[0] for l in open(E+'/PCXR_IN_PIN2-W2-IMPACT.tsv').read().splitlines()[1:]})
imp_in=[m for m in impact if m in plan]; imp_out=[m for m in impact if m not in plan]
s2=[m for m in ['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','AspisR1PublicSerializer.Types','AspisR1PublicSerializer.Funs'] if m in plan]
handover=sorted((set(imp_in)|set(s2))-set(ov_in))
roots=set(ov_in)|set(handover)
# transitive importers
seen=set();st=list(roots)
while st:
    x=st.pop()
    for y in rev[x]:
        if y not in seen: seen.add(y);st.append(y)
affected=seen|set(handover)           # modules whose built object must change/rebuild (overlay modules are built by W2)
ovset=set(ov_in)
rebuild=sorted(affected-ovset)
rb=set(rebuild)
# layers: longest path within rebuild subgraph (imports outside rb are ready)
topo={m:plan[m]['topo'] for m in rb}
layer={}
for m in sorted(rb,key=lambda m:topo[m]):
    layer[m]=1+max([layer[i] for i in imps[m] if i in rb],default=0)
nl=max(layer.values())
bylayer=collections.Counter(layer.values())
# overlay modules are layer 0 inputs; handover modules marked
rows=[]
for m in sorted(rb,key=lambda m:(layer[m],topo[m])):
    p=plan[m]
    rows.append(dict(module=m,layer=layer[m],src_rel=p['src_rel'],source_sha256=p['source']['sha256'],label=p['label'],
      role='handover_input' if m in handover else 'rebuild',
      imports_rebuild=[i for i in imps[m] if i in rb],imports_overlay=[i for i in imps[m] if i in ovset],imports_unchanged=[i for i in imps[m] if i not in rb and i not in ovset],
      l187_wall_s=rc[m][0],l187_peak_rss_kib=rc[m][1]))
out=dict(
 plan_sha256=hashlib.sha256(open(E+'/L187_PLAN_READ.json','rb').read()).hexdigest(),
 roots=dict(overlay_modules_in_closure=ov_in,overlay_modules_not_in_closure=ov_out,w2_impact_modules=imp_in,w2_impact_not_in_closure=imp_out,s2_type_modules=s2),
 handover_inputs=handover,
 counts=dict(closure=len(plan),rebuild=len(rb),handover_inputs_in_rebuild=len(handover),overlay_built=len(ov_in),
   importers_of_R0P_Core=len({y for y in _ if y} ) if False else None,layers=nl),
 modules_by_layer={str(k):bylayer[k] for k in sorted(bylayer)},
 modules=rows)
# importers of R0P.Core for cross-check with W2 (10,585)
s=set();st=['R0P.Core']
while st:
    x=st.pop()
    for y in rev[x]:
        if y not in s:s.add(y);st.append(y)
out['counts']['importers_of_R0P_Core_in_plan']=len(s)
out['counts']['rebuild_not_importing_R0P_Core']=len(rb-s)
json.dump(out,open(E+'/PCXR_REBUILD_SET.json','w'),separators=(',',':'))
# ---- estimate
def sim(workers,ovh):
    # list scheduling, priority = longest remaining weighted path
    w={m:rc[m][0]+ovh for m in rb}
    cp={}
    for m in sorted(rb,key=lambda m:-topo[m]):
        cp[m]=w[m]+max([cp[y] for y in rev[m] if y in rb],default=0)
    indeg={m:len([i for i in imps[m] if i in rb]) for m in rb}
    ready=[(-cp[m],m) for m in rb if indeg[m]==0];heapq.heapify(ready)
    running=[];t=0.0;done=0
    while done<len(rb):
        while ready and len(running)<workers:
            _,m=heapq.heappop(ready);heapq.heappush(running,(t+w[m],m))
        t,m=heapq.heappop(running);done+=1
        for y in rev[m]:
            if y in rb:
                indeg[y]-=1
                if indeg[y]==0:heapq.heappush(ready,(-cp[y],y))
    return t,max(cp.values())
walls=[rc[m][0] for m in rb];rss=sorted(rc[m][1] for m in rb)
def q(p):return rss[min(len(rss)-1,int(p*len(rss)))]
SIX=6*1024*1024
over6=[dict(module=m,peak_rss_kib=rc[m][1],wall_s=rc[m][0],in_rebuild=m in rb) for m in sorted(plan,key=lambda m:-rc[m][1]) if rc[m][1]>SIX]
est=dict(basis='L187 per-module receipts (research evidence/replay-l187-20261109/batches/*/results.jsonl.xz): lean -j1 -M7000 wall per module, 14101 modules, one lean process each, exit 0',
 rebuild_modules=len(rb),sum_l187_compile_wall_s=round(sum(walls),1),sum_l187_compile_wall_h=round(sum(walls)/3600,2),
 l187_wall_mean_s=round(statistics.mean(walls),2),l187_wall_median_s=round(statistics.median(walls),2),l187_wall_max_s=max(walls),
 peak_rss_kib=dict(min=rss[0],p50=q(.5),p90=q(.9),p99=q(.99),max=rss[-1]),
 over_6GiB_in_rebuild=[o for o in over6 if o['in_rebuild']],over_6GiB_whole_closure_count=len(over6),
 scenarios={})
for ovh in (3,10,40):
    for wk in (1,3,5):
        t,cpv=sim(wk,ovh)
        est['scenarios'][f'workers{wk}_overhead{ovh}s']=dict(wall_h=round(t/3600,2),critical_path_h=round(cpv/3600,2))
est['scenario_notes']='overhead = per-scope launch cost not in the lean wall (systemd-run, admission checks, dependency hashing). L187 observed 30-40 s per scope launched over ssh (L187_ESTIMATE.json); a host-local runner is expected to be nearer 3-10 s; 40 s kept as the pessimistic bound. Greedy list scheduling in dependency order, longest-remaining-path priority; assumes 5 slots always granted (Stream C share and host count may allow fewer).'
est['layer_histogram']={str(k):bylayer[k] for k in sorted(bylayer)}
json.dump(est,open(E+'/PCXR_ESTIMATE.json','w'),indent=1)
print(json.dumps(out['counts']),json.dumps(est['scenarios']),est['peak_rss_kib'],len(est['over_6GiB_in_rebuild']),len(over6),len(handover),ov_out,imp_out)
