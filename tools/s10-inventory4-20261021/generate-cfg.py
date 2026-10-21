#!/usr/bin/env python3
"""Emit symbolic sparse cut proofs; no recurrence normalization or decision tactic.
One forward-closure proof per cut, shared by all dominated call pairs.
"""
import argparse,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory4-20261021'
x=json.loads((E/'cfg.json').read_text());groups={};mapping=[];outputs={}
for r in x['functions']:
    key=json.dumps([r['edges'],r['cuts']],sort_keys=True)
    # Call line numbers differ by build; graph and cut/target relation define
    # reusable proof data, while both original coordinates remain in mapping.
    key=json.dumps([r['edges'],[(c['cut'],c['target'],c['reachable_without_cut']) for c in r['cuts']]])
    if key not in groups:groups[key]=(len(groups),r)
    index,_=groups[key]
    for n,c in enumerate(r['cuts']):mapping.append(dict(mode=r['mode'],header=r['header'],body_sha256=r['body_sha256'],path=r['path'],before_line=c['before'],after_line=c['after'],before_block=c['cut'],after_block=c['target'],theorem=f'AspisR1.OraclePortS10Dominance{index}.fact_{n}'))
for index,r in groups.values():
    ns=f'AspisR1.OraclePortS10Dominance{index}';s=f'''import OraclePortS10CFG

/-! Symbolic CFG cut facts for {r['header'].split('(')[0]}.
Exact graph extraction is hash-pinned in cfg.json; Rust execution and
source/model oracle correspondence remain separate obligations. -/
set_option autoImplicit false
namespace {ns}
open OraclePortS10CFG

inductive Edge : Nat → Nat → Prop where
'''
    for i,(a,b) in enumerate(r['edges']):s+=f'  | e{i} : Edge {a} {b}\n'
    cuts={c['cut']:set(c['reachable_without_cut']) for c in r['cuts'] if c['cut']!=0}
    for cut,reachable in cuts.items():
        s+=f'\ndef mark{cut} : Nat → Bool\n'
        for b in sorted(reachable):s+=f'  | {b} => true\n'
        s+='  | _ => false\n'
        s+=f'''\ntheorem closed{cut} : ∀ x y, Edge x y → y ≠ {cut} →
    mark{cut} x = true → mark{cut} y = true := by
  intro x y edge different marked
  cases edge with
'''
        for i,(a,b) in enumerate(r['edges']):
            if b in reachable:proof='rfl'
            elif b==cut:proof='False.elim (different rfl)'
            else:
                assert a not in reachable
                proof='by cases marked'
            s+=f'  | e{i} => exact {proof}\n'
        s+=f'\n#print axioms closed{cut}\n'
    for n,c in enumerate(r['cuts']):
        cut,target=c['cut'],c['target']
        s+=f'\ntheorem fact_{n} : Dominates Edge 0 {cut} {target} :=\n'
        if cut==0:s+=f'  root_dominates Edge 0 {target}\n'
        else:s+=f'  dominates_of_cut mark{cut} rfl rfl closed{cut}\n'
        s+=f'\n#print axioms fact_{n}\n'
    s+=f'end {ns}\n';outputs[B/'lean'/f'OraclePortS10Dominance{index}.lean']=s
assert len(mapping)==140
manifest=dict(schema='s10-pass4-lean-dominance-map-v1',cfg_sha256=hashlib.sha256((E/'cfg.json').read_bytes()).hexdigest(),modules=len(groups),facts=mapping,
    proof_shape='explicit edge constructors; sparse Boolean cut marks; one symbolic forward-closure case proof per cut; no decide, norm_num, general unfolding or large arithmetic')
outputs[E/'dominance-map.json']=json.dumps(manifest,indent=2,sort_keys=True)+'\n'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
for path,s in outputs.items():
    if a.check:assert path.read_text()==s,path
    else:path.write_text(s)
print(json.dumps(dict(modules=len(groups),mapped_observations=140,generated_bytes=sum(len(s.encode()) for s in outputs.values()))))
