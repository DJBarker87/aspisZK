#!/usr/bin/env python3
"""Strengthen every frozen dominance witness to a strict occurrence order.
No new source/machine semantics is inferred from a block graph.
"""
import argparse,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory5-20261021'
x=json.loads((B/'evidence/s10-inventory4-20261021/dominance-map.json').read_text());groups={};mapping=[];outputs={}
for fact in x['facts']:
    theorem=fact['theorem'];module,name=theorem.rsplit('.',1);index=int(module.rsplit('Dominance',1)[1]);groups.setdefault(index,{})[name]=fact
    mapping.append(dict(**fact,strict_theorem=f'AspisR1.OraclePortS10StrictOrder{index}.{name}'))
for index,facts in groups.items():
    s=f'''import OraclePortS10StrictOrder
import OraclePortS10Dominance{index}

/-! Earlier block occurrence on every path reaching the selected later call.
Exact graph/source coordinates are retained in strict-order-map.json. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder{index}
open OraclePortS10CFG OraclePortS10StrictOrder
'''
    for name,f in facts.items():
        before,after=f['before_block'],f['after_block'];assert before!=after
        s+=f'''
theorem {name} {{visits : List Nat}}
    (path : Path OraclePortS10Dominance{index}.Edge 0 {after} visits) :
    BeforeEnd {before} {after} visits :=
  before_end OraclePortS10Dominance{index}.{name} (by omega) path

#print axioms {name}
'''
    s+=f'end AspisR1.OraclePortS10StrictOrder{index}\n';outputs[B/'lean'/f'OraclePortS10StrictOrder{index}.lean']=s
outputs[E/'strict-order-map.json']=json.dumps(dict(schema='s10-pass5-strict-order-v1',facts=mapping,counts=dict(observations=len(mapping),distinct_theorems=sum(len(f) for f in groups.values())),input_sha256=hashlib.sha256((B/'evidence/s10-inventory4-20261021/dominance-map.json').read_bytes()).hexdigest(),scope='CFG occurrence chronology only; no caller program equality, mutable-state identification or query-loop movement is inferred.'),indent=2,sort_keys=True)+'\n'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
for p,s in outputs.items():
    if args.check:assert p.read_text()==s,p
    else:p.write_text(s)
print(json.dumps(dict(modules=len(groups),observations=len(mapping))))
