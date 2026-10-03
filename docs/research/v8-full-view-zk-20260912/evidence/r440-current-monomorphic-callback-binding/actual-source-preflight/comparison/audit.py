#!/usr/bin/env python3
"""Independent, strict structural audit of saved R437 and R440 LLBC artifacts."""
import copy,hashlib,json
from collections import Counter
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r440-mono-closure-binding/actual-source-preflight/comparison'
R437=ROOT/'.r21-scratch/r437-pointer-source-boundary/root-launch-a/saved-output/R437PointerWrapperLayout.llbc'
R440=ROOT/'.r21-scratch/r440-mono-closure-binding/actual-source-preflight/lead-launch-a/saved-output/R440ActualMonoClosure.llbc'
PINS={'R437':'bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c','R440':'01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load_exp(k):return json.loads((OUT/f'{k.lower()}-expanded.json').read_text())
assert sha(R437)==PINS['R437'] and sha(R440)==PINS['R440']
raw={k:json.loads(p.read_text()) for k,p in [('R437',R437),('R440',R440)]}
assert all(r['has_errors'] is False for r in raw.values())
A={k:load_exp(k) for k in ('R437','R440')}
assert all(A[k]['charon_version']==raw[k].get('charon_version') for k in A)
a,b=A['R437']['translated'],A['R440']['translated']
assert A['R437']['charon_version']==A['R440']['charon_version']
assert len(a['fun_decls'])==len(b['fun_decls'])==159
assert [None if x is None else x['def_id'] for x in a['fun_decls']]==[None if x is None else x['def_id'] for x in b['fun_decls']]
# Declaration tables other than functions are byte-semantic equal after strict expansion.
table_report={}
for key in ('type_decls','global_decls','trait_decls','trait_impls'):
 assert a[key]==b[key],f'unexpected table difference: {key}'
 table_report[key]={'count':len(a[key]),'canonical_sha256':hashlib.sha256(json.dumps(a[key],sort_keys=True,separators=(',',':')).encode()).hexdigest(),'exact':True}
# Read all 16 callsite paths and source-owned target IDs from the already-pinned inventory.
inv=json.loads((ROOT/'.r21-scratch/r440-mono-closure-binding/actual-source-preflight/inventory/fn-pointer-closure-inventory.json').read_text())
assert inv['source']['sha256']==PINS['R437']
sites=inv['fn_family']['closure_trait_call_sites']
assert len(sites)==16

def get(root,path):
 x=root
 for p in path:x=x[p]
 return x

def item_name(row):return row.get('item_meta',{}).get('name')
site_report=[]
for s in sites:
 path=s['path']; oldcall=get(a,path)['call']; newcall=get(b,path)['call']
 assert {k:v for k,v in oldcall.items() if k!='func'}=={k:v for k,v in newcall.items() if k!='func'},path
 oldreg=oldcall['func']['Regular']; oldkind=oldreg['kind']
 assert 'Trait' in oldkind
 tref,slot=oldkind['Trait']; assert slot==s['method_slot']
 ir=tref['kind']['TraitImpl']; assert ir['id']==s['impl_id']
 assert s['source_owner_match_status']=='unique' and len(s['source_owned_method_fun_ids'])==1
 target=s['source_owned_method_fun_ids'][0]
 newreg=newcall['func']['Regular']; assert newreg['kind']=={'Fun':{'Regular':target}},(path,newreg['kind'],target)
 # Check the emitted instantiated args against the exact outer impl args plus the old
 # method-call args in each namespace; do not erase or canonicalize any region.
 genfields=('regions','types','const_generics','trait_refs')
 expected={}
 for f in genfields:
  expected[f]=ir['generics'][f]+oldreg['generics'][f]
  assert newreg['generics'][f]==expected[f],(path,f,expected[f],newreg['generics'][f])
 owner=next(f for f in a['fun_decls'] if isinstance(f,dict) and f['def_id']==target)
 assert owner['src']['TraitImpl']['impl_ref']['id']==s['impl_id']
 assert owner['src']['TraitImpl']['item_id']=={'Method':slot}
 statement_path=path[:-1]
 site_report.append({'owner_fun_id':s['owner_fun_id'],'path':path,'old_impl_id':ir['id'],'method_slot':slot,'source_owned_target_fun_id':target,'generic_args_exact_outer_plus_inner':expected,'call_other_fields_exact':True})
# Whole function rows compare strictly once only the 16 authorized function-pointer subtrees
# are replaced by a fixed marker at their inventory-specified paths.
fa,fb=copy.deepcopy(a['fun_decls']),copy.deepcopy(b['fun_decls'])
for s in sites:
 path=s['path']
 # path is relative to translated; omit leading fun_decls to address aligned row list.
 pa=path[1:]; get(fa,pa)['call']['func']={'AUDIT_ALLOWED_CALL_FUNC'}; get(fb,pa)['call']['func']={'AUDIT_ALLOWED_CALL_FUNC'}
assert fa==fb,'unexpected function declaration/body/signature/source differences outside the 16 Call.func nodes'
# Short-name vector order is not a declaration body. Compare exact key/value maps, rejecting dupes.
def keyed_short(rows):
 out={}
 for r in rows:
  key=json.dumps(r['key'],sort_keys=True,separators=(',',':'))
  assert key not in out,'duplicate short_names key'
  out[key]=r['value']
 return out
short_a,short_b=keyed_short(a['short_names']),keyed_short(b['short_names'])
assert short_a==short_b
# All other translated fields, including files/spans/source text/metadata, compare literally,
# except output destination and order/group sequence handled as separate audits below.
rest_a,rest_b=copy.deepcopy(a),copy.deepcopy(b)
for tr in (rest_a,rest_b):
 tr.pop('ordered_decls')
 tr.pop('short_names')
 tr.pop('fun_decls')
 tr['options'].pop('dest_file')
assert rest_a==rest_b,'unexpected translated metadata/source/options differences beyond destination and separately-audited order/name vector'
# Ordered declarations: require valid group shapes, no duplicate entries, and preserve exact
# Rec/NonRec group shapes. Do not normalize Rec groups or claim coverage equality.
def groups(tr):
 out=[]
 for ix,g in enumerate(tr['ordered_decls']):
  assert isinstance(g,dict) and len(g)==1
  kind,inner=next(iter(g.items())); assert kind in ('Type','Fun','Global','TraitDecl','TraitImpl')
  assert isinstance(inner,dict) and len(inner)==1
  group_kind,members=next(iter(inner.items()))
  if group_kind=='NonRec': mem=[members]
  else: assert group_kind=='Rec' and isinstance(members,list);mem=members
  out.append({'index':ix,'kind':kind,'group_kind':group_kind,'members':mem})
 return out
ga,gb=groups(a),groups(b)
def flat(gs):return Counter((g['kind'],i) for g in gs for i in g['members'])
ca,cb=flat(ga),flat(gb)
assert all(v==1 for v in ca.values()) and all(v==1 for v in cb.values())
# Validate IDs against all declaration arrays.
tables={'Type':a['type_decls'],'Fun':a['fun_decls'],'Global':a['global_decls'],'TraitDecl':a['trait_decls'],'TraitImpl':a['trait_impls']}
for gs in (ga,gb):
 for g in gs:
  for i in g['members']:assert 0<=i<len(tables[g['kind']]) and tables[g['kind']][i] is not None,(g['kind'],i)
# Exact item coverage delta, with full native names, and check newly included functions are
# source-owned targets of changed call expressions. Do not conflate it with sequence reorder.
added=sorted(cb-ca);removed=sorted(ca-cb)
name_rows={k:tables[k] for k in tables}
def label(k,i):return item_name(name_rows[k][i])
added_rows=[{'kind':k,'id':i,'name':label(k,i)}for k,i in added]
removed_rows=[{'kind':k,'id':i,'name':label(k,i)}for k,i in removed]
assert len(added)==3 and all(k=='Fun' for k,i in added)
assert {i for k,i in added} <= {s['source_owned_method_fun_ids'][0] for s in sites}
assert len(removed)==5 and all(k=='TraitImpl' for k,i in removed)
# Changed call references explicitly identify each removed impl where present and all added targets.
old_impls={s['old_impl_id'] for s in site_report};new_targets={s['source_owned_target_fun_id'] for s in site_report}
removed_impl_ids={i for k,i in removed}; removed_direct_targets=removed_impl_ids & old_impls; removed_non_call_impls=removed_impl_ids - old_impls
added_fun_ids={i for k,i in added};assert added_fun_ids<=new_targets
# Group/SCC census and sequence facts.
assert all(g['group_kind']=='NonRec' for g in ga+gb)
# Check topological position for direct target/caller pairs only when the caller is part
# of ordered_decls. An unselected function body does not contribute an emitted graph node.
pos_b={(g['kind'],i):g['index'] for g in gb for i in g['members']}
for s in site_report:
 caller_pos=pos_b.get(('Fun',s['owner_fun_id'])); target_pos=pos_b.get(('Fun',s['source_owned_target_fun_id']))
 s['caller_in_ordered_decls']=caller_pos is not None
 s['target_in_ordered_decls']=target_pos is not None
 s['direct_target_precedes_caller_when_caller_selected']=None if caller_pos is None else (target_pos is not None and target_pos < caller_pos)
 if caller_pos is not None: assert target_pos is not None and target_pos < caller_pos,s
# Existing pinned dependency visitor source is included by exact hash; this records rules basis.
pinned=ROOT/'.r21-scratch/r288-private-batch-ordering/pinned-reorder_decls.rs'
pinned_sha=sha(pinned); assert pinned_sha=='8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632'
# Extraction command comparison: only observer executable and destination path change; flags,
# start roots/includes/features/source hashes remain equal.
cmd_a=json.loads((R437.parent/'extract-command.json').read_text());cmd_b=json.loads((R440.parent/'extract-command.json').read_text())
assert cmd_a['start_from']==cmd_b['start_from'] and cmd_a['include']==cmd_b['include']
for k in ('features','monomorphize','environment','source_hashes'):assert cmd_a[k]==cmd_b[k],k
assert cmd_a['base_extract_command_sha256']==cmd_b['base_extract_command_sha256']
ca0,cb0=cmd_a['command'][:],cmd_b['command'][:]
# Only command element 0 and the --dest-file value differ.
assert ca0[0]!=cb0[0]
def scrub_command(c):
 c=list(c);c[0]='<driver>'
 i=c.index('--dest-file'); c[i+1]='<destination>'
 return c
assert scrub_command(ca0)==scrub_command(cb0)
result_a=json.loads((R437.parent/'result.json').read_text());result_b=json.loads((R440.parent/'result.json').read_text())
assert result_a['charon_exit_status']==0 and result_b['charon_exit_status']==0 and result_a['gnu_time_exit_status']==0 and result_b['gnu_time_exit_status']==0
assert result_a['llbc_sha256']==PINS['R437'] and result_b['llbc_sha256']==PINS['R440']
assert result_a['swap_count']==result_b['swap_count']==0
assert result_a['source_hashes_before_after']['before']==result_a['source_hashes_before_after']['after']
assert result_b['source_hashes_before_after']['before']==result_b['source_hashes_before_after']['after']
assert result_a['source_hashes_before_after']['before']==result_b['source_hashes_before_after']['before']
# Literal diff path partition must be exactly the audited structures.
literal=json.loads((OUT/'literal-expanded-diff.json').read_text());assert literal['diff_count']==778
path_counts=Counter(tuple(d['path'][1:2]) for d in literal['diffs'])
assert path_counts==Counter({('short_names',):537,('ordered_decls',):188,('fun_decls',):52,('options',):1}),path_counts
report={
 'status':'PASS_STRUCTURAL_CHECKS_WITH_EXPLICIT_ORDERED_COVERAGE_DELTA; no semantic or security claim',
 'inputs':{'R437':{'path':str(R437.relative_to(ROOT)),'sha256':sha(R437),'bytes':R437.stat().st_size,'has_errors':False},'R440':{'path':str(R440.relative_to(ROOT)),'sha256':sha(R440),'bytes':R440.stat().st_size,'has_errors':False}},
 'strict_hashcons_expansion':{'R437_entries':507,'R440_entries':481,'cycles_or_missing_refs':'none; expansion completed fail-closed','no_region_generic_erasure':True},
 'literal_diff':{'path':str((OUT/'literal-expanded-diff.json').relative_to(ROOT)),'sha256':sha(OUT/'literal-expanded-diff.json'),'count':778,'partition':{k[0]:v for k,v in path_counts.items()}},
 'declaration_tables_exact':table_report,
 'functions':{'table_length':159,'non_null_count':sum(x is not None for x in a['fun_decls']),'all_ids_and_null_slots_same_order':True,'only_differences_are_the_16_call_func_nodes':True,'all_function_rows_equal_after_replacing_only_these_exact_nodes':True,'call_sites':site_report},
 'short_names':{'baseline_count':len(a['short_names']),'candidate_count':len(b['short_names']),'exact_key_value_map_equal':True,'vector_order_differs':True},
 'ordered_decls':{'R437_groups':len(ga),'R440_groups':len(gb),'all_groups_nonrecursive':True,'R437_group_kind_counts':dict(Counter(g['kind'] for g in ga)),'R440_group_kind_counts':dict(Counter(g['kind'] for g in gb)),'exact_coverage_added':added_rows,'exact_coverage_removed':removed_rows,'coverage_equal':False,'removed_impls_also_direct_call_targets':sorted(removed_direct_targets),'removed_impls_not_direct_call_targets':sorted(removed_non_call_impls),'added_funs_are_source_owned_call_targets':sorted(added_fun_ids),'all_ids_valid_and_unique':True,'candidate_direct_targets_before_selected_callers':all(s['direct_target_precedes_caller_when_caller_selected'] is True for s in site_report if s['caller_in_ordered_decls']),'call_sites_with_unselected_caller':[{'caller':s['owner_fun_id'],'target':s['source_owned_target_fun_id']} for s in site_report if not s['caller_in_ordered_decls']],'native_reorder_source_path':str(pinned.relative_to(ROOT)),'native_reorder_source_sha256':pinned_sha,'full_dependency_graph_reconstruction':'not performed in this audit; group coverage delta is reported explicitly, no assertion that membership is equal'},
 'translated_fields_other_than_functions_and_separately_audited_name_order_and_ordered_decls_exact':True,
 'options_destination':{'R437':a['options']['dest_file'],'R440':b['options']['dest_file'],'only_options_difference':'dest_file'},
 'run_receipts':{'R437':{'exit':result_a['charon_exit_status'],'wall_time':result_a['wall_time'],'max_rss_kib':result_a['peak_rss_kib'],'swap_count':result_a['swap_count'],'gnu_exit':result_a['gnu_time_exit_status']},'R440':{'exit':result_b['charon_exit_status'],'wall_time':result_b['wall_time'],'max_rss_kib':result_b['peak_rss_kib'],'swap_count':result_b['swap_count'],'gnu_exit':result_b['gnu_time_exit_status'],'source_hashes_stable_before_after':True}},
 'extract_command':{'same_start_from_include_features_monomorphize_environment_source_hashes_and_base_command_sha256':True,'base_llbc_sha256':{'R437':cmd_a['baseline_sha256'],'R440':cmd_b['baseline_sha256'],'same':cmd_a['baseline_sha256']==cmd_b['baseline_sha256']},'only_command_argv_differences':['driver executable','--dest-file value']},
 'scope':'Saved-artifact structural comparison only. No build, semantic correspondence, source correctness, or security/release conclusion.'}
(OUT/'structural-audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':report['status'],'call_site_count':len(site_report),'group_delta_added':added_rows,'group_delta_removed':removed_rows,'short_names_map_equal':True,'report_sha256':sha(OUT/'structural-audit.json')},indent=2))
