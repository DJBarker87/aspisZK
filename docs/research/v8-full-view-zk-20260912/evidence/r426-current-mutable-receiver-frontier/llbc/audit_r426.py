import json, hashlib, pathlib
ROOT=pathlib.Path(__file__).resolve().parents[3]
# The inputs are frozen, inventoried LLBC snapshots; this script only decodes JSON.
inputs={
 'R419': ROOT/'.r21-scratch/r419-try-fold-equality-elimination/runs/aspis-r419-candidate-1790967913444473000/candidate.llbc',
 'R396': ROOT/'.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc',
}
OUT=pathlib.Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def span(node):
 s=node.get('span') if isinstance(node,dict) else None
 if not s and isinstance(node,dict): s=node.get('item_meta',{}).get('span')
 try:
  d=s['data']; b=d['beg']; e=d['end']; return {'file_id':d['file_id'],'begin':b,'end':e}
 except Exception: return None

def walk(node,path='$'):
 if isinstance(node,dict):
  yield node,path
  for k,v in node.items(): yield from walk(v,path+'/'+str(k))
 elif isinstance(node,list):
  for i,v in enumerate(node): yield from walk(v,path+'/'+str(i))

def compact_ops(body, target_local):
 copies=[]; local_mentions=[]
 def rec(node,path='$',nearest=None):
  if isinstance(node,dict):
   if 'id' in node and 'kind' in node:
    kind=node['kind']; kname=next(iter(kind)) if isinstance(kind,dict) else kind
    nearest={'statement_id':node['id'],'statement_kind':kname,'statement_span':span(node)}
   if 'Copy' in node and isinstance(node['Copy'],dict):
    op=node['Copy']; k=op.get('kind',{}); loc=k.get('Local') if isinstance(k,dict) else None
    copies.append({'path':path,'local':loc,'type':op.get('ty'),'statement':nearest})
   k=node.get('kind')
   if isinstance(k,dict) and 'Local' in k and k['Local']==target_local:
    local_mentions.append({'path':path,'kind_parent_keys':list(node.keys()),'statement':nearest})
   for key,value in node.items(): rec(value,path+'/'+str(key),nearest)
  elif isinstance(node,list):
   for ix,value in enumerate(node): rec(value,path+'/'+str(ix),nearest)
 rec(body)
 return copies,local_mentions

all_data={}; bodyrows={}; compare=[]
for label,p in inputs.items():
 d=json.loads(p.read_text())['translated']
 data={'input_path':str(p.relative_to(ROOT)),'input_sha256':sha(p),'llbc_options':d['options'],'selected':{}}
 for i in (58,120,169):
  row=d['fun_decls'][i]; raw=json.dumps(row,sort_keys=True,separators=(',',':')).encode()
  name=row['item_meta'].get('name'); body=row['body']
  entry={'id':i,'name':name,'row_sha256':hashlib.sha256(raw).hexdigest(),'row':row,
         'body_kind':'Opaque' if isinstance(body,str) else 'Structured'}
  if isinstance(body,dict):
   st=body['Structured']; locals_=st['locals']['locals']; copy_sites,mentions=compact_ops(st['body'],1)
   entry.update({'body_sha256':hashlib.sha256(json.dumps(body,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
                 'body_span':span(st),'bound_body_regions':st.get('bound_body_regions'),
                 'arg_count':st['locals']['arg_count'],'locals':locals_,
                 'copy_operands':copy_sites,'local1_mentions':mentions,
                 'top_level_statement_kinds':[list(x['kind'].keys()) if isinstance(x.get('kind'),dict) else x.get('kind') for x in st['body'].get('statements',[])]})
  data['selected'][str(i)]=entry
 all_data[label]=data
 (OUT/f'{label}-selected-functions.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
# resolve type-dedup 166 via first explicit HashConsedValue occurrence
r419=json.loads(inputs['R419'].read_text())['translated']
occ=[]
for n,path in walk(r419):
 if n.get('HashConsedValue') and isinstance(n['HashConsedValue'],list) and n['HashConsedValue'][0]==166:
  occ.append({'path':path,'hashconsed_type':n['HashConsedValue']})
# recursively get matching local operand copy site for all selected rows and compare counts
for i in (58,120,169):
 a=all_data['R419']['selected'][str(i)]; b=all_data['R396']['selected'][str(i)]
 compare.append({'id':i,'R419_name':a['name'],'R396_name':b['name'],'R419_body_kind':a['body_kind'],'R396_body_kind':b['body_kind'],
                 'R419_row_sha256':a['row_sha256'],'R396_row_sha256':b['row_sha256'],
                 'R419_body_sha256':a.get('body_sha256'),'R396_body_sha256':b.get('body_sha256'),
                 'R419_copy_count':len(a.get('copy_operands',[])),'R396_copy_count':len(b.get('copy_operands',[])),
                 'R419_local1_copy_count':sum(x['local']==1 for x in a.get('copy_operands',[])),'R396_local1_copy_count':sum(x['local']==1 for x in b.get('copy_operands',[])),
                 'R419_local1_ast_mentions':len(a.get('local1_mentions',[])),'R396_local1_ast_mentions':len(b.get('local1_mentions',[])),
                 'body_ast_equal_exact':a.get('body_sha256')==b.get('body_sha256')})
# find exact failing path, statement path, types and structured local
r=r419['fun_decls'][58]['body']['Structured'];
loop=r['body']['statements'][6]['kind']['Loop']; call=loop['statements'][1]['kind']['Call']['call']
report={'inputs':{k:{'path':str(v.relative_to(ROOT)),'sha256':sha(v)} for k,v in inputs.items()},
 'R425_failure':{'wall_time_seconds':0.77,'peak_rss_kib':142032,'swap_bytes':0,'result_path':'.r21-scratch/r425-unit-constant-frontier/translation-runner/output/ee7ba72da456-20261002T210856Z/result.json','status':'exit 2; diagnostic described in retained translate.log/result; no Lean outputs'},
 'R419_error_span_trait_method':{'trait_decl_id':0,'method_index':0,'qualified_name':'core::iter::traits::iterator::Iterator::next','lang_item':'next','body':'none/default trait-method declaration; the 78:4–78:45 span belongs to method item metadata'},
 'R419_failing_copy':{'function_id':58,'qualified_name':'core::iter::traits::iterator::Iterator::try_fold','loop_statement_index':1,
  'path':'translated.fun_decls[58].body.Structured.body.statements[6].kind.Loop.statements[1].kind.Call.call.args[0]',
  'span':span(loop['statements'][1]),'callee':call['func'],'argument':call['args'][0],
  'local1':r['locals']['locals'][1],'arg_count':r['locals']['arg_count'],'bound_body_regions':r.get('bound_body_regions'),
  'resolved_type_evidence_for_Deduplicated166':occ,
  'local1_lifetime_observation':'local1 is an input local (index 1), with no explicit StorageLive/StorageDead entry for local1 in this serialized body. It is copied at this loop call. This is a serialized-body structural observation, not a borrow-checker liveness conclusion.'},
 'selected_comparison':compare,
 'R396_extraction':{'plan_path':'.r21-scratch/r396-private-batch-unmonomorphized-plan/R396-extraction-plan.json','plan_sha256':sha(ROOT/'.r21-scratch/r396-private-batch-unmonomorphized-plan/R396-extraction-plan.json'),
  'command_path':'.r21-scratch/r396-private-batch-unmonomorphized-plan/extract-command.json','command_sha256':sha(ROOT/'.r21-scratch/r396-private-batch-unmonomorphized-plan/extract-command.json'),
  'extract_log_sha256':sha(ROOT/'.r21-scratch/r396-private-batch-unmonomorphized-plan/extract.log'),
  'mir':'built','precise_drops':False,'skip_borrowck':False,'monomorphize':False,
  'note':'R396 configuration selects --mir built; saved LLBC options say precise_drops false, skip_borrowck false, monomorphize false. These are Charon extraction settings, not a saved rustc MIR dump or MIR CopyForDeref provenance.'}}
(OUT/'copy-frontier-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({'report':str(OUT/'copy-frontier-report.json'),'comparisons':compare,'resolved166_count':len(occ)},indent=2))
