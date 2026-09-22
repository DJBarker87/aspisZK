#!/usr/bin/env python3
"""Reassociate single-use additive/product regions; preserve shared boundaries.

Every local region is checked as a signed integer linear combination or an
exact factor multiset. This is an executable algebra certificate, not Lean.
"""
import argparse, collections, hashlib, heapq, json
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dag',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--pairwise',action='store_true',help='reproduce the intermediate count-balanced C candidate')
    a=p.parse_args(); old=json.loads(a.dag.read_text()); nodes=old['nodes']; uses=collections.Counter(j for n in nodes for j in n.get('args',[]))
    out=[nodes[0]]; depths=[0]; memo={0:0}; certificates=[]
    def gate(op,x,y):
        out.append({'op':op,'args':[x,y]});depths.append(1+max(depths[x],depths[y]));return len(out)-1
    def balanced(items,op):
        assert items
        if a.pairwise:
            while len(items)>1:
                items=[gate(op,items[i],items[i+1]) if i+1<len(items) else items[i] for i in range(0,len(items),2)]
            return items[0]
        queue=[(depths[i],i) for i in items];heapq.heapify(queue)
        while len(queue)>1:
            _,x=heapq.heappop(queue);_,y=heapq.heappop(queue)
            j=gate(op,x,y);heapq.heappush(queue,(depths[j],j))
        return queue[0][1]
    def emit(i):
        if i in memo:return memo[i]
        n=nodes[i]
        if n['op'] in ('input','const'):
            out.append(n);depths.append(0);result=len(out)-1
        elif n['op'] in ('add','sub'):
            terms=collections.Counter()
            def walk(j,s,force=False):
                v=nodes[j]
                if v['op'] in ('add','sub') and (force or uses[j]==1):
                    walk(v['args'][0],s);walk(v['args'][1],s if v['op']=='add' else -s)
                else:terms[j]+=s
            walk(i,1,True); terms={j:s for j,s in terms.items() if s}
            boundaries={emit(j):s for j,s in terms.items()}
            # emit never merges distinct old nonzero nodes, so no coefficient collisions.
            assert len(boundaries)==len(terms)
            pos=[j for j,s in boundaries.items() for _ in range(max(s,0))]
            neg=[j for j,s in boundaries.items() for _ in range(max(-s,0))]
            lp=balanced(pos,'add') if pos else 0
            result=gate('sub',lp,balanced(neg,'add')) if neg else lp
            def expand(j):
                if j in boundaries:return collections.Counter({j:1})
                if j==0:return collections.Counter()
                v=out[j];assert v['op'] in ('add','sub')
                c=expand(v['args'][0]);d=expand(v['args'][1])
                for t,s in d.items():c[t]+=s if v['op']=='add' else -s
                return collections.Counter({t:s for t,s in c.items() if s})
            assert dict(expand(result))==boundaries
            certificates.append({'old':i,'new':result,'kind':'integer-linear','terms':sorted(terms.items())})
        else:
            assert n['op']=='mul'; factors=[]
            def walk(j,force=False):
                v=nodes[j]
                if v['op']=='mul' and (force or uses[j]==1):
                    for t in v['args']:walk(t)
                else:factors.append(j)
            walk(i,True); mapped=[emit(j) for j in factors]; boundary=set(mapped)
            result=balanced(mapped,'mul')
            def expand(j):
                if j in boundary:return [j]
                v=out[j];assert v['op']=='mul'
                return expand(v['args'][0])+expand(v['args'][1])
            assert collections.Counter(expand(result))==collections.Counter(mapped)
            certificates.append({'old':i,'new':result,'kind':'factor-multiset','factors':factors})
        memo[i]=result;return result
    result=emit(old['output'])
    new={'input_count':old['input_count'],'output':result,'nodes':out}
    a.output.mkdir();(a.output/'source-dag.json').write_text(json.dumps(new,separators=(',',':'))+'\n')
    (a.output/'reassociation.json').write_text(json.dumps({'input_sha256':hashlib.sha256(a.dag.read_bytes()).hexdigest(),
        'old_nodes':len(nodes),'new_nodes':len(out),'checked_regions':len(certificates),'regions':certificates,
        'rule':'single-use associative rings; integer coefficients and factor multisets checked','source_refinement_proved':False},indent=2)+'\n')
    print(json.dumps({'old_nodes':len(nodes),'new_nodes':len(out),'checked_regions':len(certificates)}))
if __name__=='__main__':main()
