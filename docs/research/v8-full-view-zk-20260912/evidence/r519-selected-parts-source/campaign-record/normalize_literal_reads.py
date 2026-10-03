#!/usr/bin/env python3
"""Narrow source-value projection for exact captured U32 named-constant reads."""
import json,hashlib,copy
from pathlib import Path
H=Path(__file__).resolve().parent
SRC=H/'R519SharedGammaPartsSelection.rewrapped.llbc'
OUT=H/'R519SharedGammaPartsLiteralReads.llbc'
AUD=H/'literal-read-normalization-audit.json'
IN_SHA='4757453fd82b979c510025b2e83ae8ddd149014a3d1cbf0e753e4d3d36bc6d07'
KEEP={94,107,109,175,248}; TARGETS={31,48}
sha=lambda b:hashlib.sha256(b).hexdigest()
b=SRC.read_bytes();assert sha(b)==IN_SHA,sha(b)
x=json.loads(b); t=x['translated']; assert x['has_errors'] is False
# Complete fresh wrapper map; expand only for type-equality/audit comparisons.
hc={}
def collect(z):
 if isinstance(z,dict):
  if set(z)=={'HashConsedValue'}:
   i,v=z['HashConsedValue'];assert isinstance(i,int)
   if i in hc:assert hc[i]==v,('conflicting wrapper',i)
   else:hc[i]=v
   collect(v)
  else:
   for v in z.values():collect(v)
 elif isinstance(z,list):
  for v in z:collect(v)
collect(x)
def ex(z,seen=()):
 if isinstance(z,dict):
  if set(z)=={'HashConsedValue'}:
   i,v=z['HashConsedValue'];assert i not in seen,('cycle',(*seen,i));return ex(v,(*seen,i))
  if set(z)=={'Deduplicated'}:raise AssertionError(('unexpected Deduplicated',z))
  return {k:ex(v,seen) for k,v in z.items()}
 if isinstance(z,list):return [ex(v,seen) for v in z]
 return z
# Exact named declarations and captured compiler literal facts.
expected={31:('aspis_core::field::P','2147483647','U32'),48:('core::num::<u32>::MAX','4294967295','U32')}
global_facts={}
def ids_name(row):
 return [a['Ident'][0] for a in row['item_meta']['name'] if 'Ident' in a]
for gid,(name,val,scalar) in expected.items():
 g=t['global_decls'][gid]; assert g is not None
 decoded=ex(g); path='::'.join(ids_name(g))
 assert decoded['global_kind']=='NamedConst' and decoded['generics']['types']==[] and decoded['generics']['const_generics']==[]
 assert decoded['value']['kind']=={'Literal':{'Scalar':{'Unsigned':[scalar,val]}}},(gid,decoded['value']['kind'])
 assert ex(g['ty'])==ex(g['value']['ty']),('global/value type mismatch',gid)
 global_facts[gid]={'name':path,'global_kind':decoded['global_kind'],'declared_ty':decoded['ty'],'value':decoded['value'],'span':decoded['item_meta']['span'],'source_text':decoded['item_meta'].get('source_text'),'type_exact_after_hashcons_expansion':ex(g['ty'])==ex(g['value']['ty']),'source_file':t['files'][decoded['item_meta']['span']['data']['file_id']]['name']}
# Locate every global Place occurrence before modifying anything. The first FunsAnalysis candidate follows source declaration group order.
original=json.loads(json.dumps(x)); refs=[]
def visit(z,path,fun_id,nearest_span=None,nearest_id=None):
 if isinstance(z,dict):
  if 'span' in z and 'kind' in z and isinstance(z.get('span'),dict): nearest_span=z['span']; nearest_id=z.get('id',nearest_id)
  if set(z)=={'Copy'}:
   p=z['Copy']; k=p.get('kind',{}) if isinstance(p,dict) else {}
   gl=k.get('Global') if isinstance(k,dict) else None
   if isinstance(gl,dict) and gl.get('id') in TARGETS:
    gid=gl['id'];refs.append({'fun_id':fun_id,'global_id':gid,'path':list(path),'statement_span':nearest_span,'nested_statement_id':nearest_id,'operand':copy.deepcopy(z),'operand_ty_expanded':ex(p['ty'])})
  for k,v in z.items():visit(v,path+(k,),fun_id,nearest_span,nearest_id)
 elif isinstance(z,list):
  for i,v in enumerate(z):visit(v,path+(i,),fun_id,nearest_span,nearest_id)
for i in sorted(KEEP):
 f=t['fun_decls'][i]
 if f is not None and isinstance(f.get('body'),dict) and 'Structured' in f['body']:
  visit(f['body'],('translated','fun_decls',i,'body'),i)
assert len(refs)==5,[(r['fun_id'],r['global_id'],r['path']) for r in refs]
assert {(r['fun_id'],r['global_id']) for r in refs}=={(248,31),(175,31),(175,48)}
for r in refs:
 gid=r['global_id']; assert r['operand_ty_expanded']==ex(t['global_decls'][gid]['ty'])==ex(t['global_decls'][gid]['value']['ty']),r
# The ordered declaration traversal's earliest function-backed global reference is in Fun248 at statement-list index 13.
first=next(r for r in refs if r['fun_id']==248 and r['global_id']==31)
assert first['path'][4:7]==['Structured','body','statements'] and first['path'][7]==13,first['path']
# Record diagnostic facts separately before authorized rewrite.
diagnostic={
 'input_sha256':IN_SHA,'global_facts':global_facts,'global_reference_count':len(refs),
 'references':refs,'first_funsanalysis_global_candidate':first,
 'pinned_funsanalysis_file_sha256':'bb46649cb8466a7bf028df8f0baa6af1367e900d6cff0ad4157cab30085fe580',
 'pinned_funsanalysis_site':'FunsAnalysis.ml:176, Option.get(init_fun_id_of_global global)',
 'pinned_ga_utils_sha256':'4631c556d08ed2f4f3c7b9f73087d343651104ac9c01f150199d18087b3ec1a6',
 'ga_utils_behavior':'init_fun_id_of_global returns Some only for CCall(FunId(FRegular id), []); otherwise None',
 'r490_comparison':{
  'input_sha256':'384d170f403306449c7435e81da6050ae3f447b28a9ab0dc881450c9322621af',
  'literal_globals':[{'id':7,'value':'Usize(4)'},{'id':8,'value':'Usize(1)'}],
  'route':'fresh zero-input function-backed initializers, only in a scratch candidate; exact global.ty and value.ty refs were identical',
  'r519_literal_type_comparison':'both declared ty and value.ty independently decode to Literal UInt U32; original hashcons wrapper IDs differ, decoded types equal'
 },
 'capture_source_file_sha256':{'aspis_core_field_rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499'},
 'failure_assignment':{
  'function':'aspis_core::field::r91_raw_add','fun_id':248,'statement_list_index':13,'source_file_id':7,
  'source_path':global_facts[31]['source_file'],
  'source_span':{'beg':{'line':3229,'col':55},'end':{'line':3229,'col':59}},
  'global_reference_column_zero_based':58,
  'source_excerpt':'fn r91_raw_add(a:M31,b:M31)->M31 {let s=a.0+b.0;M31(if s>=P{s-P}else{s})',
  'failure_log':'saved-output/aeneas.log',
  'inference_limit':'The translator backtrace identifies FunsAnalysis.ml:176 but carries no function/span. Fun248 is first body in retained ordered groups after foreign Fun109, and this is the earliest retained PlaceGlobal operand read; this is therefore the first failing-source candidate. Later reads are in Fun175.'
 }
}
(H/'global-literal-read-inventory.json').write_text(json.dumps(diagnostic,indent=2,sort_keys=True)+'\n')
# Narrow authorized transformation: only Copy operands that directly refer to these exact globals.
changed=[]
def rewrite(z,path,fun_id,nearest_span=None,nearest_id=None):
 if isinstance(z,dict):
  if 'span' in z and 'kind' in z and isinstance(z.get('span'),dict): nearest_span=z['span']; nearest_id=z.get('id',nearest_id)
  if set(z)=={'Copy'}:
   p=z['Copy']; k=p.get('kind',{}) if isinstance(p,dict) else {}; gl=k.get('Global') if isinstance(k,dict) else None
   if isinstance(gl,dict) and gl.get('id') in TARGETS:
    gid=gl['id']; g=t['global_decls'][gid]
    assert ex(p['ty'])==ex(g['ty'])==ex(g['value']['ty'])
    old=copy.deepcopy(z); new={'Constant':copy.deepcopy(g['value'])}
    changed.append({'fun_id':fun_id,'global_id':gid,'path':list(path),'span':nearest_span,'nested_statement_id':nearest_id,'old_operand':old,'new_operand':copy.deepcopy(new),'old_operand_ty_expanded':ex(p['ty']),'literal_ty_expanded':ex(g['value']['ty'])})
    return new
  return {k:rewrite(v,path+(k,),fun_id,nearest_span,nearest_id) for k,v in z.items()}
 if isinstance(z,list):return [rewrite(v,path+(i,),fun_id,nearest_span,nearest_id) for i,v in enumerate(z)]
 return z
for i in sorted(KEEP):
 f=t['fun_decls'][i]
 if f is not None and isinstance(f.get('body'),dict) and 'Structured' in f['body']:
  f['body']=rewrite(f['body'],('translated','fun_decls',i,'body'),i)
assert len(changed)==len(refs)==5
# Independent exact-diff check: decode and compare to an independently edited deep copy of the source projection.
expected_out=copy.deepcopy(original)
for rec in changed:
 parent=expected_out
 for key in rec['path'][:-1]:parent=parent[key]
 parent[rec['path'][-1]]=copy.deepcopy(rec['new_operand'])

def firstdiff(a,b,p=()):
 if type(a)!=type(b): return p,a,b
 if isinstance(a,dict):
  if a.keys()!=b.keys(): return p,'keys:'+str(a.keys()),'keys:'+str(b.keys())
  for k in a:
   q=firstdiff(a[k],b[k],p+(k,))
   if q:return q
 elif isinstance(a,list):
  if len(a)!=len(b):return p,'len:'+str(len(a)),'len:'+str(len(b))
  for i,(u,v) in enumerate(zip(a,b)):
   q=firstdiff(u,v,p+(i,))
   if q:return q
 elif a!=b:return p,a,b
 return None
diff=firstdiff(ex(t),ex(expected_out)['translated'])
assert diff is None,repr(diff)[:2000]
assert {r['global_id'] for r in changed}==TARGETS
out=(json.dumps(x,ensure_ascii=False,separators=(',',':'))+'\n').encode(); OUT.write_bytes(out)
report={'status':'PASS','input_sha256':IN_SHA,'output_sha256':sha(out),'changed_operand_count':len(changed),'changed_operands':changed,'global_facts':global_facts,'all_exact_global_and_operand_types_match_after_hashcons_decode':True,'all_other_decoded_AST_fields_unchanged':True,'allowed_change':'only Copy(Global31|Global48) operand nodes become Constant(existing captured global.value)','unmodified_global_rows':True,'unmodified_functions_outside_selected_closure':True,'translation_status':'not yet run'}
AUD.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','output_sha256':sha(out),'changed_operand_count':len(changed),'first_failure_candidate':first,'globals':{k:{'name':v['name'],'value':v['value']['kind'],'type_exact_after_expansion':v['type_exact_after_hashcons_expansion']} for k,v in global_facts.items()}},indent=2))
