#!/usr/bin/env python3
"""Read-only count and shape audit for R312's Option language-item prepass."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
R327=HERE.parent/'r327-private-batch-source-try-fold/R327PrivateBatchSourceTryFold.llbc'
EXPECTED='9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
assert hashlib.sha256(R327.read_bytes()).hexdigest()==EXPECTED
raw=json.loads(R327.read_text());tr=raw['translated'];hc={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:
   i,v=x['HashConsedValue']; assert i not in hc or hc[i]==v; hc[i]=v;collect(v)
  elif 'Deduplicated' not in x:
   for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(raw)
def dec(x,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:
   i,v=x['HashConsedValue'];return {'cycle_hashcons_id':i} if i in seen else dec(v,seen+(i,))
  if 'Deduplicated'in x:
   i=x['Deduplicated'];assert i in hc;return {'cycle_hashcons_id':i} if i in seen else dec(hc[i],seen+(i,))
  return {k:dec(v,seen) for k,v in x.items()}
 if isinstance(x,list):return [dec(v,seen) for v in x]
 return x

types={r['def_id']:r for r in tr['type_decls'] if isinstance(r,dict)}
def base_name(row):
 return '::'.join(p['Ident'][0] for p in row.get('item_meta',{}).get('name') or [] if 'Ident'in p)
def inst_args(row):
 for p in row.get('item_meta',{}).get('name') or []:
  if 'Instantiated'in p:return [dec(x) for x in p['Instantiated'].get('skip_binder',{}).get('types',[])]
 return []
def pp(x,seen=()):
 if isinstance(x,dict):
  if 'Adt'in x:
   adt=x['Adt'];ident=adt.get('id');args=[pp(dec(a),seen) for a in adt.get('generics',{}).get('types',[])]
   if isinstance(ident,dict) and isinstance(ident.get('Adt'),int):
    tid=ident['Adt'];r=types.get(tid);name=base_name(r) if r else f'Adt{tid}'
    if r and not args and tid not in seen:
     args=[pp(a,seen+(tid,)) for a in inst_args(r)]
   elif ident=='Tuple':return '()'
   else:name=str(ident)
   return name+('<'+', '.join(args)+'>' if args else '')
  if 'Ref'in x:
   region,ty,mut=x['Ref'];return '&'+('mut ' if mut=='Mut' else '')+pp(ty,seen)
  if 'Literal'in x:
   lit=x['Literal'];
   if 'UInt'in lit:return {'Usize':'usize','U32':'u32','U64':'u64'}.get(lit['UInt'],str(lit['UInt']))
   return str(lit)
  if 'TypeVar'in x:return 'TypeVar'
  return '<'+next(iter(x))+'>'
 return str(x)

def variant_summary(r):
 kind=dec(r.get('kind'))
 if not isinstance(kind,dict) or 'Enum' not in kind:return {'kind':str(kind)}
 return [{'variant_id':v.get('id'),'name':v.get('name'),'fields':[{'name':f.get('name'),'type':pp(f.get('ty'))} for f in v.get('fields',[])],
          'discriminant':v.get('discriminant')} for v in kind['Enum']]

options=[]
for r in tr['type_decls']:
 if isinstance(r,dict) and r.get('item_meta',{}).get('lang_item')=='Option':
  options.append({'def_id':r['def_id'],'base_name':base_name(r),'lang_item':r['item_meta'].get('lang_item'),
                  'opacity':r['item_meta'].get('opacity'),'is_local':r['item_meta'].get('is_local'),
                  'source_origin':dec(r.get('src')),'item_span':r['item_meta'].get('span'),
                  'instantiated_type_args':[pp(a) for a in inst_args(r)],
                  'generics':dec(r.get('generics')),'variants':variant_summary(r),
                  'x86_64_layout':next((v for v in dec(r.get('layout',[])) if v.get('key')=='x86_64-unknown-linux-gnu'),None)})
assert len(options)==3,[(x['def_id'],x['base_name']) for x in options]

fun_decls={r['def_id']:r for r in tr['fun_decls'] if isinstance(r,dict)}
def ret_path_scan(body):
 found=[]
 def rec(x,path='$',loop_depth=0):
  if isinstance(x,dict):
   if x.get('kind')=='Return':found.append({'path':path,'nested_under_loop':loop_depth>0,'loop_depth':loop_depth,'statement_id':x.get('id'),'span':x.get('span')})
   if isinstance(x.get('kind'),dict) and 'Loop' in x['kind']:
    b=x['kind']['Loop'];loop_span=b.get('span'); nextdepth=loop_depth+1
    for k,v in x.items():
     if k=='kind':
      for j,w in b.items():rec(w,path+'.kind.Loop.'+j,nextdepth)
     else:rec(v,path+'.'+k,loop_depth)
    return
   for k,v in x.items():rec(v,path+'.'+k,loop_depth)
  elif isinstance(x,list):
   for i,v in enumerate(x):rec(v,f'{path}[{i}]',loop_depth)
 rec(body)
 return found
functions=[]
for fid in (36,38):
 r=fun_decls[fid];body=dec(r['body'])['Structured'];ret_local=body['locals']['locals'][0]
 sigout=dec(r['signature']['output']);localty=dec(ret_local['ty'])
 assert sigout==localty
 returns=ret_path_scan(body['body'])
 assert len([x for x in returns if x['nested_under_loop']])==1 and len(returns)==2
 # Type id of concrete return ADT.
 out_adt=sigout.get('Adt',{}).get('id',{}).get('Adt')
 functions.append({'def_id':fid,'name':base_name(r),'source_origin':dec(r.get('src')),
                   'signature_output_decoded':sigout,'return_type_pretty':pp(sigout),'return_local0_type_matches_signature':True,
                   'return_type_decl_id':out_adt,'generic_regions':dec(r['generics']).get('regions'),
                   'generic_type_count':len(r['generics'].get('types',[])),
                   'loop_nodes':[{'path':'$.body.statements[4].kind.Loop','source_span':body['body']['statements'][4]['kind']['Loop']['span']}],
                   'return_nodes':returns})

prepasses=HERE/'pinned-source/PrePasses.candidate.ml'
sourcehash=hashlib.sha256(prepasses.read_bytes()).hexdigest()
assert sourcehash=='09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd'
r312result=json.loads((HERE.parent/'r312-slice-length-tool-candidate/build-result.json').read_text())
r330cmd=json.loads((HERE.parent/'r330-sourceful-batch-translation/translate-command.json').read_text())
r330result=json.loads((HERE.parent/'r330-sourceful-batch-translation/translation-result.json').read_text())
r330log=(HERE.parent/'r330-sourceful-batch-translation/translate.log').read_text()
assert r312result['binary_sha256']==r330cmd['binary_sha256']=='fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f'
assert r330cmd['source_sha256']==EXPECTED and r330result['translator_exit_status']==2
assert 'Nested-loop returns require exactly one Option language item' in r330log
report={'scope':'read-only source/LLBC inventory; no translation, build, extraction, or Lean run',
 'input_llbc_sha256':EXPECTED,'has_errors':raw['has_errors'],'charon_version':raw['charon_version'],
 'R312_prepasses':{'candidate_sha256':sourcehash,'parent_sha256':'eb060cdec736ea1f5d222c42160d5f50ad20bd651c8f7c08baf56896c1835e68',
                   'compiled_R312_binary_sha256':r312result['binary_sha256'],'function':'lower_nested_loop_returns',
                   'source_line_range':'PrePasses.candidate.ml:940–1050',
                   'mechanical_condition':'For a function containing Return under a Loop, it collects all type declarations whose item_meta.lang_item is Option and requires exactly one; it then uses body.locals.locals[0].local_ty as return_ty and constructs Option<return_ty>.',
                   'excerpt_file':'pinned-source/lower_nested_loop_returns.excerpt.txt'},
 'option_language_item_inventory':{'count':len(options),'rows':options},
 'function_return_and_loop_return_inventory':functions,
 'current_R330_translation_failure':{'input_sha256':r330cmd['source_sha256'],'binary_sha256':r330cmd['binary_sha256'],
   'exit_status':r330result['translator_exit_status'],'generated_dir_exists':r330result['generated_dir_exists'],
   'message':'Nested-loop returns require exactly one Option language item',
   'source':'/rustc/library/core/src/iter/traits/iterator.rs:2486:4–2490:35',
   'pass_location':'PrePasses.ml:969; lower_nested_loop_returns',
   'wall_time':'0:00.16','max_rss_kib':64768,'swaps':0},
 'no_decision':'This report only inventories the exact prepass condition and LLBC rows. It does not recommend an Option-selection rule or other change.'}
(HERE/'option-return-preflight.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'option_lang_item_declarations':len(options),'rows':[(x['def_id'],x['instantiated_type_args'],[v['name'] for v in x['variants']]) for x in options],
 'functions':[(x['def_id'],x['return_type_pretty'],sum(y['nested_under_loop'] for y in x['return_nodes'])) for x in functions],
 'R330_current_first_failure':report['current_R330_translation_failure']['message']},indent=2))
