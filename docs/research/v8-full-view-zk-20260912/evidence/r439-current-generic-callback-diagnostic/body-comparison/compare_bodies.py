#!/usr/bin/env python3
"""Compare complete callback bodies, preserving raw rows and all regions."""
import collections,hashlib,json,os
from pathlib import Path
O=Path(__file__).resolve().parent
P437=O/'input/R437PointerWrapperLayout.llbc'; P438=O/'input/R438GenericClosureDispatch.llbc'
A=json.loads(P437.read_text());B=json.loads(P438.read_text());TA=A['translated'];TB=B['translated']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x):(O/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def makehc(t):
 hc={}
 def walk(x):
  if isinstance(x,dict):
   if set(x)=={'HashConsedValue'}:
    q=x['HashConsedValue']
    if not isinstance(q,list) or len(q)!=2 or not isinstance(q[0],int):raise ValueError('malformed HashConsedValue')
    if q[0] in hc and hc[q[0]]!=q[1]:raise ValueError(f'conflicting hashcons {q[0]}')
    hc[q[0]]=q[1]
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(t);return hc
HA,HB=makehc(TA),makehc(TB)
def expand(x,hc,active=()):
 if isinstance(x,dict):
  if set(x)=={'HashConsedValue'}:return expand(x['HashConsedValue'][1],hc,active)
  if set(x)=={'Deduplicated'}:
   i=x['Deduplicated']
   if i not in hc:raise ValueError(f'missing hashcons {i}')
   if i in active:raise ValueError(f'hashcons cycle {active+(i,)}')
   return expand(hc[i],hc,active+(i,))
  return {k:expand(v,hc,active) for k,v in x.items()}
 if isinstance(x,list):return [expand(v,hc,active) for v in x]
 return x
FA=expand(TA['fun_decls'][112],HA); FB=expand(TB['fun_decls'][284],HB)
# A declaration-ID mapping is explicit and limited to names established from
# exact declarations/source paths/signatures. Region indices are never mapped.
IDMAP={'fun':{24:20,124:321,112:284},'type':{50:65},'trait_decl':{3:9},'trait_impl':{35:47},'adt':{50:65}}

def stmt_envelope(x):
 return isinstance(x,dict) and all(k in x for k in ('span','id','kind','comments_before'))
def canonical(x,path=(),parent_key=None):
 if isinstance(x,dict):
  out={}
  isstmt=stmt_envelope(x)
  for k,v in x.items():
   if k=='span':continue
   if isstmt and k=='id':continue
   if k=='def_id' and path==() and isinstance(v,int): v=IDMAP['fun'].get(v,v)
   if k=='Regular' and parent_key=='Fun' and isinstance(v,int): v=IDMAP['fun'].get(v,v)
   if k=='id' and isinstance(v,dict) and set(v)=={'Adt'} and isinstance(v['Adt'],int):
    v={'Adt':IDMAP['adt'].get(v['Adt'],v['Adt'])}
   if k=='Adt' and isinstance(v,list) and v and isinstance(v[0],int):
    v=[IDMAP['adt'].get(v[0],v[0]),*v[1:]]
   if k=='TraitImpl' and isinstance(v,dict) and isinstance(v.get('id'),int):
    vv=dict(v);vv['id']=IDMAP['trait_impl'].get(vv['id'],vv['id']);v=vv
   if k=='Trait' and isinstance(v,int):v=IDMAP['trait_impl'].get(v,v)
   if k=='id' and 'trait_ref' in path and isinstance(v,int):v=IDMAP['trait_decl'].get(v,v)
   if k=='id' and 'impl_ref' in path and isinstance(v,int):v=IDMAP['trait_impl'].get(v,v)
   out[k]=canonical(v,path+(k,),k)
  return out
 if isinstance(x,list):return [canonical(v,path+(i,),parent_key) for i,v in enumerate(x)]
 return x
CA,CB=canonical(FA),canonical(FB)

def diffs(a,b,path=()):
 if type(a)!=type(b):return [{'path':list(path),'kind':'type','left':a,'right':b}]
 if isinstance(a,dict):
  out=[]
  for k in sorted(set(a)|set(b)):
   if k not in a:out.append({'path':list(path+(k,)),'kind':'missing_left','right':b[k]})
   elif k not in b:out.append({'path':list(path+(k,)),'kind':'missing_right','left':a[k]})
   else:out.extend(diffs(a[k],b[k],path+(k,)))
  return out
 if isinstance(a,list):
  out=[]
  if len(a)!=len(b):out.append({'path':list(path),'kind':'length','left':len(a),'right':len(b)})
  for i,(x,y) in enumerate(zip(a,b)):out.extend(diffs(x,y,path+(i,)))
  return out
 if a!=b:return [{'path':list(path),'kind':'value','left':a,'right':b}]
 return []
D=diffs(CA,CB)
def cat(d):
 p=d['path']
 if 'on_unwind' in p:return 'unwinds'
 if any(k in ('regions','region','regions_outlive','types_outlive') for k in p):return 'regions'
 if any(k in ('generics','types','trait_refs','trait_clauses','trait_type_constraints','const_generics') for k in p):return 'generics_types'
 if any(isinstance(v,str) and v in ('Ref','Deref','Move','Copy','Assign','Call','Aggregate','Loop','Switch','Drop','StorageDead','StorageLive') for v in p):return 'code_operations'
 return 'other_structure'
cats=collections.Counter(cat(d) for d in D)

# Extract all referenced function IDs from complete bodies, including drop fn_ptrs.
def scan_ids(x,path=(),out=None):
 if out is None:out=[]
 if isinstance(x,dict):
  if 'Fun' in x:
   f=x['Fun']
   if isinstance(f,dict) and 'Regular' in f:out.append({'path':list(path+('Fun','Regular')),'id':f['Regular']})
  for k,v in x.items():scan_ids(v,path+(k,),out)
 elif isinstance(x,list):
  for i,v in enumerate(x):scan_ids(v,path+(i,),out)
 return out
refsA=scan_ids(FA['body']); refsB=scan_ids(FB['body'])

# Store exact selected rows, both raw serialized and expanded; all type/region
# annotations survive these rows unchanged.
rows={'inputs':{'R437':{'path':str(P437),'sha256':sha(P437),'has_errors':A['has_errors'],'charon_version':A['charon_version']},'R438':{'path':str(P438),'sha256':sha(P438),'has_errors':B['has_errors'],'charon_version':B['charon_version']},'relation_callback_source_sha256_R437':hashlib.sha256(TA['files'][0]['contents'].encode()).hexdigest(),'relation_callback_source_sha256_R438':hashlib.sha256(TB['files'][0]['contents'].encode()).hexdigest()},'raw':{'R437_Fun112':TA['fun_decls'][112],'R438_Fun284':TB['fun_decls'][284]},'expanded':{'R437_Fun112':FA,'R438_Fun284':FB}}
dump('raw-and-expanded-fun112-fun284.json',rows)
dump('canonical-structural-views.json',{'id_mapping':IDMAP,'R437_Fun112':CA,'R438_Fun284':CB,'normalization':'Only all source-span fields and the id field of recognized structured-statement envelopes are omitted; explicit nominal ID bijection is applied to function/trait/type references. All generic and region annotations are retained.'})
dump('structural-diff.json',{'id_mapping':IDMAP,'equal_after_named_id_mapping_and_span_statement_id_omission':len(D)==0,'diff_count':len(D),'category_counts':dict(cats),'diffs':D})

# Collect exact selected declarations used to justify nominal renamings.
def decrow(table,i,hc):return expand(table[i],hc)
map_evidence=[]
for label,table,ids,hc in [
 ('R437 function',TA['fun_decls'],[24,124,112],HA),('R438 function',TB['fun_decls'],[20,321,284],HB),
 ('R437 type',TA['type_decls'],[2,50],HA),('R438 type',TB['type_decls'],[2,65],HB),
 ('R437 trait_decl',TA['trait_decls'],[3],HA),('R438 trait_decl',TB['trait_decls'],[9],HB),
 ('R437 trait_impl',TA['trait_impls'],[35],HA),('R438 trait_impl',TB['trait_impls'],[47],HB)]:
 for i in ids:map_evidence.append({'side':label,'id':i,'row':decrow(table,i,hc)})
dump('nominal-id-bijection-evidence.json',{'id_mapping':IDMAP,'basis':'Exact declaration rows, names, source_text where present, and fully hash-cons-expanded signatures; no region or generic field discarded.','declarations':map_evidence})

# Fail closed if the source-derived declaration names/signatures do not support
# the human-readable labels used below.
def last_ident(name):
 return name[-1]['Ident'][0] if isinstance(name,list) and name and 'Ident' in name[-1] else None
for trans,fid,mname in [(TA,24,'mul'),(TA,124,'add'),(TB,20,'mul'),(TB,321,'add')]:
 row=trans['fun_decls'][fid]
 name=expand(row['item_meta']['name'],HA if trans is TA else HB)
 hc=HA if trans is TA else HB
 assert name[0]['Ident'][0]=='aspis_core' and name[1]['Ident'][0]=='field'
 assert last_ident(name)==mname
 assert name[2]['Impl']['Ty']['skip_binder']['Adt']['id']['Adt']==2
 sig=expand(row['signature'],hc)
 assert sig['inputs']==[
  {'Adt':{'generics':{'const_generics':[],'regions':[],'trait_refs':[],'types':[]},'id':{'Adt':2}}},
  {'Adt':{'generics':{'const_generics':[],'regions':[],'trait_refs':[],'types':[]},'id':{'Adt':2}}}]
 assert sig['output']=={'Adt':{'generics':{'const_generics':[],'regions':[],'trait_refs':[],'types':[]},'id':{'Adt':2}}}
for trans in (TA,TB):
 assert last_ident(trans['type_decls'][2]['item_meta']['name'])=='QM31'

# Categorize unnormalized path changes with exact JSON paths. No premise or
# semantic inference is made from matching/differing outputs.
report={'inputs':rows['inputs'],'function_ids':{'R437':112,'R438':284},'declaration_mapping':IDMAP,'reference_id_occurrences':{'R437':refsA,'R438':refsB},'normalized_diff_count':len(D),'normalized_diff_categories':dict(cats),'diff_paths_by_category':{k:[d for d in D if cat(d)==k] for k in sorted(cats)},'source_boundary':'Only the callback bodies are compared. Only spans and statement-envelope IDs are ignored. All region annotations/generics remain in the structural comparison. No semantic equivalence claim.'}
dump('comparison-report.json',report)

# Explicitly inventory nested statement lists, unwind payloads, operation tags,
# and every Free/Bound region occurrence so equality is not inferred from a
# list-length diff alone.
def body_inventory(row):
 statement_lists=[]; operations=collections.Counter(); regions=[]; unwind_paths=[]
 def walk(x,path=()):
  if isinstance(x,dict):
   if isinstance(x.get('statements'),list):
    statement_lists.append({'path':list(path+('statements',)),'count':len(x['statements'])})
   if 'on_unwind' in x:unwind_paths.append(list(path+('on_unwind',)))
   if 'kind' in x and isinstance(x['kind'],dict) and len(x['kind'])==1:
    operations[next(iter(x['kind']))]+=1
   if set(x)=={'Var'} and isinstance(x['Var'],dict):
    regions.append({'path':list(path),'value':x['Var']})
   for k,v in x.items():walk(v,path+(k,))
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,path+(i,))
 walk(row)
 return {'statement_lists':statement_lists,'total_statements':sum(x['count'] for x in statement_lists),'operation_kind_counts':dict(operations),'on_unwind_paths':unwind_paths,'region_annotations':regions,'region_annotation_count':len(regions)}
invA,invB=body_inventory(CA),body_inventory(CB)
dump('body-shape-audit.json',{'normalization':'Same explicit nominal ID mapping and omission of source spans/statement-envelope IDs as structural-diff.json. Region annotations are recorded with exact structural paths and values; none are omitted.','R437_Fun112':invA,'R438_Fun284':invB,'statement_list_inventory_equal':invA['statement_lists']==invB['statement_lists'],'operation_kind_counts_equal':invA['operation_kind_counts']==invB['operation_kind_counts'],'on_unwind_paths_equal':invA['on_unwind_paths']==invB['on_unwind_paths'],'region_annotations_equal':invA['region_annotations']==invB['region_annotations']})

lines=['# R437 Fun112 vs R438 Fun284 complete callback-body comparison','',
 f"R437 input SHA-256: `{sha(P437)}`; R438 input SHA-256: `{sha(P438)}`.",
 f"Embedded `relation_callback.rs` SHA-256: R437 `{report['inputs']['relation_callback_source_sha256_R437']}`, R438 `{report['inputs']['relation_callback_source_sha256_R438']}`.",
 'The exact raw declaration rows and fully hash-cons-expanded rows, including every statement and `on_unwind` subtree, are retained in `raw-and-expanded-fun112-fun284.json`. The structural view omits source-span fields and only the `id` field on recognized statement envelopes; it preserves generics, all region annotations, all other declaration IDs, every operation, and all unwind/drop bodies. A narrowly stated nominal-reference bijection is applied and separately evidenced.', '',
 '## Nominal declaration ID bijection', '',
 '|R437|R438|Identity basis|','|---|---:|---|',
 '|Fun24 `aspis_core::field::QM31::mul`|Fun20|Same decoded name path and `QM31 × QM31 → QM31` signature (all inputs/output are Type2); source definition IDs differ.|',
 '|Fun124 `aspis_core::field::QM31::add`|Fun321|Same decoded name path and `QM31 × QM31 → QM31` signature (all inputs/output are Type2); source definition IDs differ.|',
 '|Type50 closure `freeze::closure::2::closure::0`|Type65|Exact same source text and name path, two captured-field struct shape; field types retain Free-region annotations.|',
 '|TraitDecl3 `core::ops::function::FnMut`|TraitDecl9|Same exact trait name path/lang item in decoded declarations.|',
 '|TraitImpl35 closure FnMut impl|TraitImpl47|Same closure source text/method slot and FnMut target after Type50→65; complete impl generics are retained in evidence.|',
 '|Type2 `aspis_core::field::QM31`|Type2|Same ID/name/kind on both inputs; unchanged mapping.|',
 '',
 'The mapping evidence, including expanded signatures and declaration rows, is in `nominal-id-bijection-evidence.json`.', '',
 '## Statements, operations, unwinds, and regions', '',
 'Each body has 36 statements in its outer list plus three nested lists of five statements each, for 51 total. Each has three `on_unwind` payloads. `body-shape-audit.json` records every nested list path, every operation-kind count, exact unwind paths, and all 31 `Free` region-annotation occurrences with their paths and values. These inventories match after the stated normalization; no region annotation is erased.', '',
 '## Structural comparison', '',
 f"Differences after the stated normalization and nominal mapping: **{len(D)}**. Category counts: `{json.dumps(dict(cats),sort_keys=True)}`.",
 'The sole remaining difference is `src.TraitImpl.trait_ref.generics.types`: R437 has two type arguments while R438 has three; the additional R438 argument is `QM31` (Type2), according to both captured Type2 declarations. It is retained as a difference, not normalized away. The 51-statement operation structure, three unwind subtrees, and all 31 region annotations match under the stated normalization.',
 'Every remaining path/value difference is recorded in `structural-diff.json`; `comparison-report.json` groups those exact paths by region/generic, operation, unwind, and other structure. No region indices were normalized or discarded. A zero diff would only mean these JSON callback bodies coincide under the recorded structural normalization; it would not establish runtime semantics or source-to-model correspondence.', '',
 'No builds, translations, or Lean jobs were run.' ]
(O/'README.md').write_text('\n'.join(lines)+'\n')
# Final independent hashes for every output except the manifest itself.
manifest=[]
for root,dirs,files in os.walk(O):
 dirs.sort()
 for name in sorted(files):
  p=Path(root)/name
  if p.name=='SHA256SUMS':continue
  manifest.append(f"{sha(p)}  {p.relative_to(O).as_posix()}")
(O/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
print(json.dumps({'diffs':len(D),'categories':dict(cats),'refs':{'R437':len(refsA),'R438':len(refsB)},'input_hashes':rows['inputs']},indent=2))
