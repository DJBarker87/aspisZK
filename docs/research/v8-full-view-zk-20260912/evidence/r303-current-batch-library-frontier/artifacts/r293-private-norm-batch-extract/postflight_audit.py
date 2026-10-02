#!/usr/bin/env python3
"""Audit saved R293 Charon output; no additional extraction or translation."""
import hashlib,json,pathlib,re
HERE=pathlib.Path(__file__).resolve().parent
SRC=HERE/'R283PrivateNormBatch.input.llbc'; OUT=HERE/'R293PrivateNormBatch.llbc'
EXPECTED_SRC='999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==EXPECTED_SRC
raw=json.loads(OUT.read_text()); t=raw['translated']
assert raw['has_errors'] is True
assert t['options']['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']

def parts(row):
 out=[]
 for item in row.get('item_meta',{}).get('name',[]):
  if 'Ident' in item: out.append(item['Ident'][0])
  elif 'Impl' in item:
   spec=item['Impl']; out.append('Impl(Trait '+str(spec['Trait'])+')' if 'Trait' in spec else 'InherentImpl')
  else: out.append(str(item))
 return out
def named(row): return '::'.join(parts(row))
fun_rows=[x for x in t.get('fun_decls',[]) if isinstance(x,dict)]
type_rows=[x for x in t.get('type_decls',[]) if isinstance(x,dict)]
selected=[]
for category, predicate, rows in [
 ('function','iterator_chain',fun_rows),('function','iterator_any',fun_rows),
 ('function','chain_next',fun_rows),('function','slice_iter_any',fun_rows),
 ('function','slice_last',fun_rows),('type','chain_type',type_rows)]:
 for x in rows:
  p=parts(x); n='::'.join(p)
  ok={
    'iterator_chain': n=='core::iter::traits::iterator::Iterator::chain',
    'iterator_any': n=='core::iter::traits::iterator::Iterator::any',
    'chain_next': n=='core::iter::adapters::chain::Impl(Trait 4)::next',
    'slice_iter_any': n=='core::slice::iter::Impl(Trait 2)::any',
    'slice_last': n=='core::slice::InherentImpl::last',
    'chain_type': n=='core::iter::adapters::chain::Chain'
  }[predicate]
  if ok:
   selected.append({'target':predicate,'kind':category,'def_id':x['def_id'],'name':n,
    'body_status':('opaque' if x.get('body')=='Opaque' else 'body-present') if category=='function' else None,
    'opacity':x.get('item_meta',{}).get('opacity'),'is_local':x.get('item_meta',{}).get('is_local'),
    'span':x.get('item_meta',{}).get('span')})
bytarget={x['target']:x for x in selected}
assert set(bytarget)=={'iterator_chain','iterator_any','chain_next','slice_iter_any','slice_last','chain_type'},set(bytarget)
assert all(bytarget[x]['body_status']=='body-present' for x in ('iterator_chain','iterator_any','chain_next','slice_iter_any','slice_last'))
log=(HERE/'extract.log').read_text()
error_note='Unsupported constant: "Cannot translate constant of union type"'
assert error_note in log
assert "core::slice::iter::{impl core::iter::traits::iterator::Iterator for core::slice::iter::Iter<'a, T>}::next_chunk" in log
m=re.search(r'Elapsed \(wall clock\) time(?: \(h:mm:ss or m:ss\))?: ([^\n]+)',log); assert m
rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',log); assert rss
swaps=re.search(r'Swaps: (\d+)',log); assert swaps
metrics={'charon_exit_status':0,'has_errors':raw['has_errors'],'llbc_sha256':sha(OUT),'input_sha256':sha(SRC),
 'source_revision_recorded':'380c7d46c9719dcfcab601fac2607861d47dee02','selected_census':selected,
 'root_fun0':{'present':any(x.get('def_id')==0 for x in fun_rows),'local':next(x for x in fun_rows if x['def_id']==0)['item_meta']['is_local'],'body_present':next(x for x in fun_rows if x['def_id']==0).get('body') not in (None,'Opaque')},
 'declaration_counts':{k:sum(isinstance(x,dict) for x in t.get(k,[])) for k in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls')},
 'typecheck_diagnostic':{'text':error_note,'source':'/rustc/library/core/src/slice/iter/macros.rs:207:33','function':"core::slice::iter::{impl Iterator for Iter<'a, T>}::next_chunk",'first_use':'../r110_norm.rs:62:38, through xs.iter().chain(ys).any(...)'},
 'gnu_time':{'wall_time':m.group(1),'peak_rss_kib':int(rss.group(1)),'swaps':int(swaps.group(1)),'exit_status':0},
 'scope':'Extraction diagnostic only. has_errors=true, so do not use as proof input. No translation performed.'}
(HERE/'postflight.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps({k:metrics[k] for k in ('charon_exit_status','has_errors','root_fun0','selected_census','typecheck_diagnostic','gnu_time')},indent=2))
