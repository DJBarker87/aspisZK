#!/usr/bin/env python3
"""Preserve selected native rows and strict R434/R437 function comparisons."""
import hashlib,json
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r437-pointer-source-boundary/type-inventory'
IN={'R434':ROOT/'.r21-scratch/r434-actual-fold-control/root-launch-a/saved-output/R434ActualFoldUbHelpers.llbc','R437':ROOT/'.r21-scratch/r437-pointer-source-boundary/root-launch-a/saved-output/R437PointerWrapperLayout.llbc'}
PIN={'R434':'7c03a7576da2d380749bdd48a9ded791e4563d6fb3b6834ef4d15665f479b96e','R437':'bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c'}
TIDS=[58,59,69,72,73]; FIDS=[43,70,86]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def capture(label,p):
 doc=json.loads(p.read_text()); assert sha(p)==PIN[label] and doc.get('has_errors') is False
 tr=doc['translated']; defs={}
 def collect(x):
  if isinstance(x,dict):
   h=x.get('HashConsedValue')
   if isinstance(h,list) and len(h)==2:
    i,v=h
    if i in defs and defs[i]!=v:raise ValueError(f'hashcons collision {i}')
    defs[i]=v
   for v in x.values():collect(v)
  elif isinstance(x,list):
   for v in x:collect(v)
 collect(tr)
 def expand(x,stack=()):
  if isinstance(x,dict):
   if set(x)=={'HashConsedValue'}:
    i,_=x['HashConsedValue'];
    if i in stack:raise ValueError('hashcons cycle')
    return expand(defs[i],stack+(i,))
   if set(x)=={'Deduplicated'}:
    i=x['Deduplicated'];
    if i in stack:raise ValueError('dedup cycle')
    return expand(defs[i],stack+(i,))
   return {k:expand(v,stack) for k,v in x.items()}
  if isinstance(x,list):return [expand(v,stack) for v in x]
  return x
 return doc,tr,expand
C={k:capture(k,p) for k,p in IN.items()}
for label,(doc,tr,expand) in C.items():
 def inst_arg(i): return expand(tr['type_decls'][i]['item_meta']['name'][-1]['Instantiated']['skip_binder']['types'][0])
 q=inst_arg(58); s=inst_arg(69); ph=inst_arg(59)
 assert q.get('Adt',{}).get('id')=={'Adt':2},(label,'NonNull<QM31>',q)
 assert s.get('Slice',{}).get('Adt',{}).get('id')=={'Adt':2},(label,'NonNull<[QM31]>',s)
 assert ph.get('Ref',[None,None,None])[1].get('Adt',{}).get('id')=={'Adt':2},(label,'PhantomData<&QM31>',ph)
if True:
 _,r437,_=C['R437']
 expected_layout={58:(8,8,[0],True),59:(0,1,[],False),69:(16,8,[0],True)}
 for i,(size,align,offsets,transparent) in expected_layout.items():
  layout=r437['type_decls'][i]['layout'][0]['value']
  assert (layout['size'],layout['align'],layout['variant_layouts'][0]['field_offsets'],layout['repr']['transparent'])==(size,align,offsets,transparent),i
def name(n):
 parts=[]
 for x in n:
  if 'Ident' in x:parts.append(x['Ident'][0])
  elif 'Impl' in x:parts.append('<impl>')
  elif 'Instantiated' in x:parts.append('<instantiated>')
 return '::'.join(parts)
selected={}
for label,(doc,tr,expand) in C.items():
 p=IN[label]
 selected[label]={'capture':{'path':str(p.relative_to(ROOT)),'sha256':sha(p),'size_bytes':p.stat().st_size,'has_errors':doc['has_errors'],
  'result_path':str(p.parent/'result.json'),'result_sha256':sha(p.parent/'result.json'),'result':json.loads((p.parent/'result.json').read_text()),
  'command_path':str(p.parent/'extract-command.json'),'command_sha256':sha(p.parent/'extract-command.json'),'command':json.loads((p.parent/'extract-command.json').read_text()),
  'runner_status_path':str(p.parent/'runner-status.json'),'runner_status_sha256':sha(p.parent/'runner-status.json'),'runner_status':json.loads((p.parent/'runner-status.json').read_text())},
  'type_declarations_raw':{str(i):tr['type_decls'][i] for i in TIDS},
  'type_declarations_resolved':{str(i):expand(tr['type_decls'][i]) for i in TIDS},
  'function_rows_raw':{str(i):tr['fun_decls'][i] for i in FIDS}}
(OUT/'selected-type-and-function-rows.json').write_text(json.dumps(selected,indent=2,sort_keys=True)+'\n')
comparisons={}
for fid in [70,86]:
 norm={}
 for label,(doc,tr,expand) in C.items():
  row=expand(tr['fun_decls'][fid])
  def strip(x):
   if isinstance(x,dict):
    st={'id','kind','span','comments_before'}<=set(x)
    return {k:strip(v) for k,v in x.items() if k not in ('span','generated_from_span') and not(st and k=='id')}
   if isinstance(x,list):return [strip(v) for v in x]
   return x
  norm[label]=strip(row)
 diff=[]
 def cmp(a,b,path='$'):
  if type(a)!=type(b):diff.append({'path':path,'old_type':type(a).__name__,'new_type':type(b).__name__});return
  if isinstance(a,dict):
   if set(a)!=set(b):diff.append({'path':path,'old_keys':sorted(a),'new_keys':sorted(b)});return
   for k in a:cmp(a[k],b[k],path+'/'+k)
  elif isinstance(a,list):
   if len(a)!=len(b):diff.append({'path':path,'old_len':len(a),'new_len':len(b)});return
   for i,(x,y) in enumerate(zip(a,b)):cmp(x,y,f'{path}/{i}')
  elif a!=b:diff.append({'path':path,'old':a,'new':b})
 cmp(norm['R434'],norm['R437'])
 comparisons[str(fid)]={'equal':not diff,'difference_count':len(diff),'differences':diff,'old_sha256':PIN['R434'],'new_sha256':PIN['R437'],
  'normalization':'Expand capture-local hashcons/dedup independently; ignore only span/generated_from_span and id on recognized statement rows.'}
(OUT/'function-body-comparisons.json').write_text(json.dumps(comparisons,indent=2,sort_keys=True)+'\n')
summaries={}
for label,(doc,tr,expand) in C.items():
 summaries[label]={str(i):{'qualified_name':name(tr['type_decls'][i]['item_meta']['name']),
  'instantiated_name_tail_raw':tr['type_decls'][i]['item_meta']['name'][-1].get('Instantiated'),
  'instantiated_name_tail_resolved':expand(tr['type_decls'][i]['item_meta']['name'][-1].get('Instantiated')),
  'generics':tr['type_decls'][i].get('generics'),'body':tr['type_decls'][i].get('kind'),
  'non_doc_attributes':[a for a in tr['type_decls'][i]['item_meta'].get('attr_info',{}).get('attributes',[]) if 'DocComment' not in a],
  'layout':tr['type_decls'][i].get('layout'),'ptr_metadata':tr['type_decls'][i].get('ptr_metadata'),'source_kind':tr['type_decls'][i].get('src'),
  'target_information':doc['translated'].get('target_information')} for i in TIDS}
(OUT/'type-shape-summary.json').write_text(json.dumps(summaries,indent=2,sort_keys=True)+'\n')
print(json.dumps({'inputs':PIN,'function_comparisons':{i:v['equal'] for i,v in comparisons.items()},'type_ids':TIDS}))
