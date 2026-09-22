#!/usr/bin/env python3
"""Compile fixed layer wiring into reduced ordered multi-terminal diagrams.

Every represented Boolean triple is reconstructed independently and compared
with the complete sparse gate table. Skipped variables mean a full subcube,
not permission to omit a constraint. No field sampling is used for this check.
"""
import argparse, hashlib, itertools, json
from pathlib import Path

def diagram(points, order):
    nodes, intern = [], {}
    def rec(items, depth):
        if not items: return 0
        if depth == len(order):
            assert len(items) == 1
            return items[0][1]
        bit = order[depth]
        low = rec([t for t in items if not t[0] >> bit & 1], depth + 1)
        high = rec([t for t in items if t[0] >> bit & 1], depth + 1)
        if low == high: return low
        key = (bit, low, high)
        if key not in intern:
            intern[key] = len(nodes) + 5
            nodes.append(key)
        return intern[key]
    root = rec(list(points.items()), 0)
    return nodes, root

def decode(nodes, root, order, bound):
    result = {}
    rank = {v:i for i,v in enumerate(order)}
    def rec(node, depth, prefix):
        if node == 0: return
        target = len(order) if node < 5 else rank[nodes[node-5][0]]
        assert target >= depth
        # Explicitly expand every skipped Boolean coordinate.
        prefixes = [prefix]
        for i in range(depth, target):
            prefixes += [x | 1 << order[i] for x in prefixes]
            assert len(prefixes) <= bound
        for x in prefixes:
            if node < 5:
                assert x not in result
                result[x] = node
                assert len(result) <= bound
            else:
                bit, low, high = nodes[node-5]
                assert low < node and high < node
                rec(low, target+1, x)
                rec(high, target+1, x | 1 << bit)
    rec(root, 0, 0)
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--circuit',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args(); c=json.loads(a.circuit.read_text())
    prev=len(c['inputs']); records=[]; generated=[]
    for index,gates in enumerate(c['layers']):
        bz=(len(gates)-1).bit_length(); k=(prev-1).bit_length()
        points={}
        for g,(op,left,right) in enumerate(gates):
            if op==4: continue
            assert op in range(4)
            points[g | left<<bz | right<<(bz+k)] = op+1
        groups=[list(range(bz)), list(range(bz,bz+k)), list(range(bz+k,bz+2*k))]
        options=[]
        for perm in itertools.permutations(range(3)):
            for reverse in [False,True]:
                gs=[list(reversed(g)) if reverse else g for g in groups]
                for interleave in [False,True]:
                    order=([v for i in range(max(bz,k)) for j in perm for v in gs[j][i:i+1]] if interleave else [v for j in perm for v in gs[j]])
                    nodes,root=diagram(points,order)
                    options.append((len(nodes),order,nodes,root))
        _,order,nodes,root=min(options)
        assert decode(nodes,root,order,len(points)+1)==points
        assert len(nodes)+5 < 65536
        generated.append((nodes,root,bz,k))
        records.append({'layer':index,'gates':len(gates),'nodes':len(nodes),'order':order,'root':root,'exact_boolean_support_checked':len(points)})
        prev=len(gates)
    lines=['// Generated fixed wiring; exact support equality checked by generator.',
           'pub struct Layer { pub nodes: &\'static [(u8,u16,u16)], pub root:usize, pub z:usize, pub k:usize }']
    for i,(nodes,root,bz,k) in enumerate(generated):
        lines.append(f'static N{i}:&[(u8,u16,u16)]=&['+','.join(f'({v},{l},{r})' for v,l,r in nodes)+'];')
    lines.append('pub static LAYERS:&[Layer]=&['+','.join(f'Layer{{nodes:N{i},root:{root},z:{bz},k:{k}}}' for i,(_,root,bz,k) in enumerate(generated))+'];')
    lines.append(f'pub const MAX_NODES:usize={max(len(n) for n,_,_,_ in generated)+5};')
    report={'source_circuit_sha256':hashlib.sha256(a.circuit.read_bytes()).hexdigest(),'layers':records,
            'total_nodes':sum(len(n) for n,_,_,_ in generated),'original_gates':sum(len(g) for g in c['layers']),
            'exact_support_equal':True,'transcript_and_proof_unchanged':True}
    a.output.mkdir()
    (a.output/'r21_wiring_tables.rs').write_text('\n'.join(lines)+'\n')
    (a.output/'wiring.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='layers'}))

if __name__=='__main__':main()
