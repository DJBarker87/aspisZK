"""Check literal-false outer gates, preserving source statement identities.

Only assignments immediately in the SAME block are used. Any call, drop,
projection write, loop or unknown control invalidates the entire bool map.
This is a structural source argument, not a machine proof of Charon semantics.
"""
from pathlib import Path
import json,lzma,hashlib,argparse
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';I=R/'imports-b3q/pv-b3q2-20261031'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
g=json.loads((I/'direct3-instantiated-callcone.json').read_text());raw=lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes());ll=json.loads(raw)['translated'];fs={f['def_id']:f for f in ll['fun_decls']if f};events=json.loads((R/'FORMATTING-EVENTS-D569.json').read_text())['events'];rows=[]
def ids(v):
 if isinstance(v,list):return [z for y in v for z in ids(y)]
 if isinstance(v,dict):return ([v['id']]if {'span','id','kind'}<=v.keys()else [])+[z for y in v.values()for z in ids(y)]
 return []
def local(op):
 for k in ['Move','Copy']:
  if k in op:return op[k]['kind'].get('Local')
def block(b,inst):
 known={}
 for st in b.get('statements',[]):
  k=st['kind']
  if not isinstance(k,dict):
   if k not in ['Nop']:known.clear()
   continue
  if 'Assign'in k:
   dest,rhs=k['Assign'];slot=dest['kind'].get('Local')
   if slot is None:known.clear();continue
   known.pop(slot,None)
   use=rhs.get('Use',[{}])[0];v=use.get('Const',{}).get('kind',{}).get('Literal',{}).get('Bool')
   if isinstance(v,bool):known[slot]=(v,st)
  elif 'Switch'in k:
   switch=k['Switch']
   if 'If'in switch:
    cond,yes,no=switch['If'];slot=local(cond)
    if slot in known:
     value,assignment=known[slot];dead=no if value else yes;contained=set(ids(dead))
     matched=[e for e in events if e['instance']==inst and e['statement']in contained]
     if matched:
      assert value is False # all currently supported certificates are disabled debug gates
      rows.append(dict(instance=inst,slot=slot,assignment=assignment,gate=dict(id=st['id'],span=st['span'],condition=cond),disabled_branch=True,events=[dict(statement=e['statement'],category=e['category'],span=e['span'])for e in matched],lemma='PV_B3P_DisabledGate571227.all_prior_states',scope='literal-false source gate; no invariant about the assertion expression is assumed'))
    block(yes,inst);block(no,inst)
   else:walk(switch,inst)
   known.clear()
  elif 'StorageDead'in k or 'StorageLive'in k:
   known.pop(k.get('StorageDead',k.get('StorageLive')),None)
  else:
   known.clear();walk(k,inst)
def walk(v,inst):
 if isinstance(v,list):
  for y in v:walk(y,inst)
 elif isinstance(v,dict):
  if 'statements'in v:block(v,inst)
  else:
   for y in v.values():walk(y,inst)
for inst,v in g['instances'].items():
 if fs[v['id']].get('body'):walk(fs[v['id']]['body'],inst)
assert len(rows)==7 and sum(len(r['events'])for r in rows)==11,[(r['instance'],r['events'])for r in rows]
x=dict(llbc_sha256=hashlib.sha256(raw).hexdigest(),graph_sha256=hashlib.sha256((I/'direct3-instantiated-callcone.json').read_bytes()).hexdigest(),certificates=rows,local_assertion_edges_excluded=7,local_index_edges_excluded=4,evidence_class='script-checked structural source argument plus generic Lean local-store law; not a proof of the whole native cone',actual_caller_composition_complete=False,source_to_machine='V370 D381/D386 retained',premises_removed=[])
p=R/'DISABLED-GATES-D571.json';s=json.dumps(x,indent=2)+'\n'
if args.check:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(disabled_source_gates=len(rows),covered_assertions=7,covered_indices=4,check=args.check)))
