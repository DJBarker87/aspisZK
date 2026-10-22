#!/usr/bin/env python3
"""Rebind each historical observation to a newly checked graph cut."""
import argparse,hashlib,json,re
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'s10-repin-20261022'
def load(p):return json.loads(p.read_text())
def callkey(c):
 # Local numbering and successor labels are compiler coordinates.
 s=re.sub(r'\bbb\d+\b','bbN',c['text'])
 return re.sub(r'\b_\d+\b','_v',s)
def build():
 old=load(B/'s10-inventory3-20261021/ordering-observations.json')
 new=load(E/'ordering-observations.json');cfg=load(E/'cfg.json')
 keys=lambda f:(f['mode'],f['header'])
 newby={keys(f):f for f in new['functions']};graphs={keys(f):f for f in cfg['functions']}
 facts=[]
 for a in old['functions']:
  b=newby[keys(a)]
  assert [callkey(c) for c in a['calls']]==[callkey(c) for c in b['calls']],keys(a)
  ac={c['line']:i for i,c in enumerate(a['calls'])};bc={c['line']:i for i,c in enumerate(b['calls'])}
  np={(bc[d['before']],bc[d['after']]):d for d in b['dominance']}
  for d in a['dominance']:
   pair=ac[d['before']],ac[d['after']];nd=np.pop(pair)
   g=graphs[keys(b)];cut=next(c for c in g['cuts'] if c['before']==nd['before'] and c['after']==nd['after'])
   reachable=set(cut['reachable_without_cut']);assert cut['target'] not in reachable
   assert (0 in reachable)==(cut['cut']!=0)
   assert all(dst==cut['cut'] or src not in reachable or dst in reachable for src,dst in g['edges'])
   facts.append(dict(mode=a['mode'],function=a['header'],selected_call_indices=list(pair),
    before_call_key=callkey(a['calls'][pair[0]]),after_call_key=callkey(a['calls'][pair[1]]),
    old=d,new=nd,new_cut=cut,old_body_sha256=a['body_sha256'],new_body_sha256=b['body_sha256'],
    block_coordinates_changed=(d['before_block'],d['after_block'])!=(nd['before_block'],nd['after_block']),
    status='REESTABLISHED_PYTHON_GRAPH_CERTIFICATE',
    scope='Exact new MIR graph cut. Generic dominance/strict chronology mathematics retained; no new Lean specialization or source/model execution identity claimed.'))
  assert not np,keys(a)
 assert len(facts)==140
 return dict(schema='s10-adopted-ordering-repin-v1',facts=facts,all_140_preserved=True,
  coordinate_changes=sum(r['block_coordinates_changed'] for r in facts),
  changed_bodies=sum(r['old_body_sha256']!=r['new_body_sha256'] for r in facts),
  explanation='TX2 inlines changed weights::powers<29>; basic-block/local numbering changes while all selected-call dominance relations persist. Old tx2 CFG specializations remain historical. The new cuts are checked independently in Python, without Lean.',
  source_order='OPEN: S2 caller identities, concrete carriers/source Calls tree and source/model ordered joins remain required',
  complete=False)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 x=build();raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode();p=E/'ordering-repin-map.json'
 if args.check:assert p.read_bytes()==raw
 else:p.write_bytes(raw)
 print(json.dumps({k:v for k,v in x.items() if k!='facts'}))
