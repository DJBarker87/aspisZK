#!/usr/bin/env python3
"""Layer the fixed source DAG with live-value copies; never accept runtime wiring.

This first pilot measures generic sparse wiring too. It does not assume the
source's regularity automatically produces a sublinear wiring evaluator.
"""
import argparse, hashlib, json
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dag',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();dag=json.loads(a.dag.read_text());nodes=dag['nodes'];output=dag['output']
    assert dag['input_count']==24 and nodes[0]=={'op':'const','constant':[0,0,0,0]}
    reachable={0,output};todo=[output]
    while todo:
        i=todo.pop();n=nodes[i]
        for j in n.get('args',[]):
            assert 0<=j<i
            if j not in reachable:reachable.add(j);todo.append(j)
    depth={};last={}
    for i,n in enumerate(nodes):
        if i not in reachable:continue
        if n['op'] in ('input','const'):depth[i]=0
        else:
            assert n['op'] in ('add','mul','sub') and len(n['args'])==2
            depth[i]=1+max(depth[j] for j in n['args'])
            for j in n['args']:last[j]=max(last.get(j,0),depth[i])
    live=sorted(i for i in reachable if depth[i]==0)
    inputs=[nodes[i] for i in live];layers=[];wiring=[]
    for d in range(1,depth[output]+1):
        old={n:i for i,n in enumerate(live)}
        nxt=sorted(i for i in reachable if depth[i]<=d and (i in (0,output) or last.get(i,0)>d))
        gates=[]
        for i in nxt:
            if depth[i]<d:gates.append([3,old[i],old[0]])
            else:
                n=nodes[i];left,right=n['args'];gates.append([{'add':0,'mul':1,'sub':2}[n['op']],old[left],old[right]])
        assert all(max(g[1:])<len(live) for g in gates)
        layers.append(gates);wiring.append({'depth':d,'live':len(nxt),'copies':sum(g[0]==3 for g in gates)})
        live=nxt
    layers.append([[3,live.index(output),live.index(0)]])
    c={'input_count':24,'inputs':inputs,'layers':layers,'scope':'ordinary+image'}
    circuit_id=hashlib.sha256(b'Aspis/R21/layered-source-circuit/v1\0'+json.dumps(c,sort_keys=True,separators=(',',':')).encode()).digest()
    lines=['// Generated fixed circuit. Do not edit; no runtime-supplied wiring.','use super::r21_gkr::{Circuit,Gate,Input};']
    lines+=['static INPUTS:&[Input]=&[']
    for n in inputs:
        if n['op']=='input':
            assert 0<=n['index']<24;lines.append(f'Input::Public({n["index"]}),')
        else:
            assert all(0<=v<2**31-1 for v in n['constant']);lines.append(f'Input::Constant({n["constant"]}),')
    lines+= ['];']
    for i,gates in enumerate(layers):
        assert len(gates)<65536
        lines.append(f'static L{i}:&[Gate]=&['+','.join(f'Gate({op},{l},{r})' for op,l,r in gates)+'];')
    lines.append('static LAYERS:&[&[Gate]]=&['+','.join(f'L{i}' for i in range(len(layers)))+'];')
    lines.append(f'pub static CIRCUIT:Circuit=Circuit{{id:{list(circuit_id)},inputs:INPUTS,layers:LAYERS}};')
    a.output.mkdir();(a.output/'r21_circuit.rs').write_text('\n'.join(lines)+'\n')
    previous=len(inputs);fields=0
    for gates in layers:
        k=(previous-1).bit_length();fields+=5*k+3;previous=len(gates)
    report={'source_dag_sha256':hashlib.sha256(a.dag.read_bytes()).hexdigest(),'circuit_id':circuit_id.hex(),
        'dag_nodes':len(nodes),'reachable_nodes':len(reachable),'layers':len(layers),'input_leaves':len(inputs),
        'max_width':max(len(inputs),*(len(g) for g in layers)),'gates_including_copies':sum(map(len,layers)),
        'copies':sum(g[0]==3 for layer in layers for g in layer),'proof_fields':fields,'proof_bytes':16*fields,
        'wiring':wiring,'native_equivalence_proved':False,'soundness_proved':False}
    (a.output/'circuit.json').write_text(json.dumps(c)+'\n')
    (a.output/'circuit-profile.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
