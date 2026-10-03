#!/usr/bin/env python3
"""R519 V3: remove only unused P/u32::MAX ordered-declaration export groups."""
import hashlib,json
from pathlib import Path
from collections import defaultdict
H=Path(__file__).resolve().parent
SRC=H/'R519SharedGammaPartsLiteralReadsV2.llbc'; OUT=H/'R519SharedGammaPartsLiteralReadsV3.llbc'; AUD=H/'ordered-global-omission-v3-audit.json'
EXPECTED='481629bdff71b10467071a7f5af21ef060c043efcb925888c1c8d5472aa76fb6'
sha=lambda b:hashlib.sha256(b).hexdigest()
sb=SRC.read_bytes(); assert sha(sb)==EXPECTED
st=sb.decode('utf-8'); raw=json.loads(sb); t=raw['translated']; assert raw['has_errors'] is False
# Independent pinned-visitor dependency census over V2.
pre=H/'post-literal-reference-audit'
sumry=json.loads((pre/'dependency-summary.json').read_text()); edges=json.loads((pre/'dependency-edges.json').read_text())
nodes=json.loads((pre/'reachable-nodes.json').read_text())
expected_nodes={('Fun',94),('Fun',107),('Fun',109),('Fun',175),('Fun',248),('Type',6),('Type',43),('Type',67)}
assert sumry['input_sha256']==EXPECTED and sumry['roots']==[['Fun',107]]
assert sumry['missing_references']==[] and sumry['unclassified_id_generics']==[]
reach={(r['kind'],r['id']) for r in nodes}; assert reach==expected_nodes,reach
assert not any(e['to'][0]=='Global' and e['available_row'] and not e['pinned_parent_suppressed'] for e in edges)
assert not any(k=='TraitDecl' or k=='TraitImpl' for k,_ in reach)
# Independently scan all retained function rows and selected type rows for direct Global31/48 references.
def scan_globals(z,path=(),out=None):
 if out is None:out=[]
 if isinstance(z,dict):
  q=z.get('Global')
  if isinstance(q,dict) and q.get('id') in (31,48):out.append({'id':q['id'],'path':list(path+('Global',))})
  for k,v in z.items():scan_globals(v,path+(k,),out)
 elif isinstance(z,list):
  for i,v in enumerate(z):scan_globals(v,path+(i,),out)
 return out
fun_refs=[]; decl_refs=[]
for k,i in sorted(reach):
 row=t[{'Fun':'fun_decls','Type':'type_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}[k]][i]
 hits=scan_globals(row,('translated',k,i))
 if k=='Fun':fun_refs += hits
 else:decl_refs += hits
assert not fun_refs,fun_refs
assert not decl_refs,decl_refs
# The two original literal declaration rows remain exactly present and unmodified.
for gid,val in ((31,'2147483647'),(48,'4294967295')):
 g=t['global_decls'][gid]; assert g['global_kind']=='NamedConst'
 assert g['value']['kind']=={'Literal':{'Scalar':{'Unsigned':['U32',val]}}}
# Confirm exact original projection groups and remove only these two rows.
old=t['ordered_decls']; assert len(old)==10
removed=[]; new=[]
for group in old:
 if group in ({'Global':{'NonRec':31}},{'Global':{'NonRec':48}}):removed.append(group)
 else:new.append(group)
assert removed==[{'Global':{'NonRec':31}},{'Global':{'NonRec':48}}],removed
newmembers=set()
for group in new:
 k,r=next(iter(group.items()));mode,ids=next(iter(r.items()));ids=[ids] if mode=='NonRec' else ids
 newmembers.update((k,i) for i in ids)
assert newmembers==reach,newmembers
# Replace only translated.ordered_decls text value. All retained source rows and complete global_decls map remain byte-identical.
needle='"ordered_decls":'; assert st.count(needle)==1
s0=st.index(needle)+len(needle); start=s0
while st[start].isspace():start+=1
_,end=json.JSONDecoder().raw_decode(st,s0)
replacement=json.dumps(new,separators=(',',':'),ensure_ascii=False)
out_text=st[:start]+replacement+st[end:]; ob=out_text.encode('utf-8'); OUT.write_bytes(ob)
check=json.loads(ob)
assert check['translated']['ordered_decls']==new
for key in raw:
 if key=='translated':
  for tk in t:
   if tk=='ordered_decls':continue
   assert check['translated'][tk]==t[tk],('changed translated field',tk)
 else: assert check[key]==raw[key],key
assert check['translated']['global_decls']==t['global_decls']
prefix=len(st[:start].encode()); suffix=len(st[:end].encode()); rbytes=len(replacement.encode())
assert ob[:prefix]==sb[:prefix] and ob[prefix+rbytes:]==sb[suffix:]
report={'status':'PASS','input_sha256':EXPECTED,'output_sha256':sha(ob),'changed_field':'translated.ordered_decls only','removed_groups':removed,'retained_group_count':len(new),'retained_group_members':sorted([list(x) for x in newmembers]),'postliteral_typed_closure_nodes':len(reach),'postliteral_typed_edge_count':len(edges),'postliteral_global_edges_reachable':0,'retained_function_global31_48_references':fun_refs,'retained_selected_type_trait_global31_48_references':decl_refs,'all_other_ordered_groups_preserved_in_order':True,'global_decls_rows_31_48_retained_exactly':True,'every_other_translated_table_structurally_unchanged':True,'prefix_suffix_bytes_identical':True,'preflight_basis':'pinned typed visitor, exact R508 source-backed projection, plus independent recursive selected-row scan','translation_status':'not yet run'}
AUD.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2))
