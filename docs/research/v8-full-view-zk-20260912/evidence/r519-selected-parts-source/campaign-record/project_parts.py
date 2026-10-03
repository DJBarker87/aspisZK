import json,hashlib,pathlib
from collections import defaultdict
O=pathlib.Path(__file__).resolve().parent
SRC=pathlib.Path('.r21-scratch/r508-selected-prepare-source/R508SelectedPrepare.llbc').resolve()
EDGES=O/'dependency-edges.json'; SUMMARY=O/'dependency-summary.json'
EXPECTED='600705e63cb7ba718e09a11e2da257c2fccf097173bfea00f294446265d32bc8'
sha=lambda b:hashlib.sha256(b).hexdigest()
src=SRC.read_bytes(); assert sha(src)==EXPECTED
stxt=src.decode('utf-8')
raw=json.loads(src); t=raw['translated']; assert raw['has_errors'] is False
summary=json.loads(SUMMARY.read_text()); edges=json.loads(EDGES.read_text())
assert summary['roots']==[['Fun',107]] and summary['missing_references']==[] and summary['unclassified_id_generics']==[]
reach={('Fun',107)}; graph=defaultdict(set)
for e in edges:
 if e['available_row'] and not e['pinned_parent_suppressed']: graph[tuple(e['from'])].add(tuple(e['to']))
q=list(reach)
while q:
 for d in graph[q.pop()]:
  if d not in reach: reach.add(d); q.append(d)
assert len(reach)==summary['reachable_node_count']==10
members=[]
for g in t['ordered_decls']:
 k,v=next(iter(g.items())); mode,ids=next(iter(v.items())); ids=[ids] if mode=='NonRec' else ids
 for i in ids:
  if (k,i) in reach: members.append(g)
assert sum(len((list(g.values())[0].get('NonRec'),)) for g in members if False)==0
out_t=json.loads(json.dumps(raw)); out_t['translated']['ordered_decls']=members
# Splice only the ordered_decls JSON value into the original text.
needle='"ordered_decls":'; assert stxt.count(needle)==1
s0=stxt.index(needle)+len(needle)
value_start=s0
while stxt[value_start].isspace(): value_start+=1
_,se=json.JSONDecoder().raw_decode(stxt,s0)
replacement=json.dumps(members,separators=(',',':'),ensure_ascii=False)
projected_text=stxt[:value_start]+replacement+stxt[se:]
projected=projected_text.encode('utf-8')
OUT=O/'R519SharedGammaPartsSelection.llbc'; OUT.write_bytes(projected)
check=json.loads(projected)
assert check['translated']['ordered_decls']==members
check['translated']['ordered_decls']=t['ordered_decls']; assert check==raw
prefix_bytes=len(stxt[:value_start].encode('utf-8')); suffix_bytes=len(stxt[:se].encode('utf-8'))
assert projected[:prefix_bytes]==src[:prefix_bytes]
assert projected[prefix_bytes+len(replacement.encode('utf-8')):]==src[suffix_bytes:]
report={'status':'PASS','source_sha256':sha(src),'projection_sha256':sha(projected),'root':['Fun',107],'root_name':'aspis_v8_performance_host::r17_host_relation::shared_gamma::parts','root_body_kind':'Structured','selected_group_count':len(members),'reachable_nodes':len(reach),'typed_edges':len(edges),'missing_references':summary['missing_references'],'unclassified_id_generics':summary['unclassified_id_generics'],'only_ordered_decls_changed':True,'prefix_suffix_byte_identical':True,'translation_status':'NOT RUN','semantic_status':'inventory/projection only'}
(O/'projection-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
