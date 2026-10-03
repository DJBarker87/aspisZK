#!/usr/bin/env python3
"""Read-only verification of the R440 Fun29 ordered_decls-only projection."""
import collections, hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
SRC=HERE/'../lead-launch-a/saved-output/R440ActualMonoClosure.llbc'
OUT=HERE/'fun29/R440GammaExecutionSelection.llbc'
SUMMARY=HERE/'fun29/inventory/dependency-summary.json'
EDGES=HERE/'fun29/inventory/dependency-edges.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
src=SRC.read_bytes(); out=OUT.read_bytes()
assert sha(src)=='01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d'
assert sha(out)=='96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48'
a=json.loads(src); b=json.loads(out); assert a['has_errors'] is b['has_errors'] is False
summary=json.loads(SUMMARY.read_text()); edges=json.loads(EDGES.read_text())
assert summary['roots']==[['Fun',29]] and summary['missing_references']==[] and summary['unclassified_id_generics']==[]
reach={('Fun',29)}; graph=collections.defaultdict(set)
for e in edges:
 if e['available_row'] and not e['pinned_parent_suppressed']: graph[tuple(e['from'])].add(tuple(e['to']))
q=list(reach)
while q:
 for t in graph[q.pop()]:
  if t not in reach: reach.add(t); q.append(t)
assert len(reach)==summary['reachable_node_count']==62
member=set()
for g in b['translated']['ordered_decls']:
 assert len(g)==1
 k,v=next(iter(g.items())); assert len(v)==1
 mode,ids=next(iter(v.items())); ids=[ids] if mode=='NonRec' else ids
 assert mode in ('NonRec','Rec') and isinstance(ids,list) and ids
 member.update((k,i) for i in ids)
assert member==reach
assert all(('Fun',i) in member for i in (24,29,70,112))
# Every JSON value except the declaration-group selection must match.
a['translated']['ordered_decls']=b['translated']['ordered_decls']
assert a==b
needle='"ordered_decls":'; st=src.decode(); ot=out.decode(); assert st.count(needle)==ot.count(needle)==1
s0=st.index(needle)+len(needle); o0=ot.index(needle)+len(needle)
_,se=json.JSONDecoder().raw_decode(st,s0); _,oe=json.JSONDecoder().raw_decode(ot,o0)
assert st[:s0]==ot[:o0] and st[se:]==ot[oe:]
print(json.dumps({'status':'PASS','input_sha256':sha(src),'projection_sha256':sha(out),'root':['Fun',29],'selected_group_count':len(b['translated']['ordered_decls']),'selected_member_count':len(member),'reachable_nodes':len(reach),'typed_edges':len(edges),'only_ordered_decls_changed':True},indent=2))
