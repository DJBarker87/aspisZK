#!/usr/bin/env python3
"""Read-only saved-artifact provenance and consistency audit for R307-R314."""
import hashlib,json,subprocess,re
from pathlib import Path
A=Path(__file__).resolve().parent; ROOT=A.parents[1]; SRC=ROOT/'.r21-scratch'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def gnu_metrics(path):
 t=path.read_text(); return {'wall_time':re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',t).group(1).strip(),'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t).group(1)),'swap_count':int(re.search(r'Swaps: (\d+)',t).group(1))}
def item_rows(translated,key): return {r['def_id']:r for r in translated[key] if isinstance(r,dict)}

def collect_hc(x,table):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in table or table[i]==v; table[i]=v; collect_hc(v,table)
  elif 'Deduplicated' not in x:
   for v in x.values(): collect_hc(v,table)
 elif isinstance(x,list):
  for v in x: collect_hc(v,table)
def decode(x,table,seen=()):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue']; assert i not in seen; return decode(v,table,seen+(i,))
  if 'Deduplicated' in x:
   i=x['Deduplicated']; assert i in table and i not in seen; return decode(table[i],table,seen+(i,))
  return {k:decode(v,table,seen) for k,v in x.items()}
 if isinstance(x,list): return [decode(v,table,seen) for v in x]
 return x

# Sourceful LLBC and projection rows.
r294=A/'inputs/R294PrivateNormBatch.llbc'; r309=A/'artifacts/r309-slice-last-with-length-projection/R309SliceLastWithLengthProjection.llbc'
assert sha(r294)=='bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f'
assert sha(r309)=='9264aea58bf430b023ed8124bf8737ef6943e97230f08aa7982648f4f7557421'
raw=load(r294); proj=load(r309); assert raw['has_errors'] is False and proj['has_errors'] is False
D=raw['translated']; P=proj['translated']; srcT={}; outT={}; collect_hc(raw,srcT); collect_hc(proj,outT)
assert len(srcT)==422 and len(outT)==19 and set(outT)<=set(srcT)
assert all(decode(v,srcT)==decode(outT[i],outT) for i,v in srcT.items() if i in outT)
source_groups={'Type':'type_decls','Fun':'fun_decls'}
ids={'Type':(9,),'Fun':(5,12)}
rowproof=[]
for kind,ks in source_groups.items():
 sr=item_rows(D,ks); pr=item_rows(P,ks)
 for i in ids[kind]:
  assert decode(sr[i],srcT)==decode(pr[i],outT)
  rowproof.append({'kind':kind,'id':i,'decoded_row_signature_body_metadata_equal':True,'decoded_row_sha256':hashlib.sha256(json.dumps(decode(sr[i],srcT),sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert D['fun_decls'][5]['item_meta']['lang_item']=='slice_len_fn'
assert D['fun_decls'][5]['body']=='Opaque' and D['fun_decls'][5]['item_meta']['opacity']=='Foreign'
assert P['fun_decls'][5]['def_id']==5 and P['fun_decls'][12]['def_id']==12
assert P['ordered_decls']==[{'Type':{'NonRec':9}},{'Fun':{'NonRec':5}},{'Fun':{'NonRec':12}}]
lengths={k:len(D[v]) for k,v in {'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}.items()}
assert lengths=={k:len(P[v]) for k,v in {'Type':'type_decls','Fun':'fun_decls','Global':'global_decls','TraitDecl':'trait_decls','TraitImpl':'trait_impls'}.items()}
# Read saved R307 metadata audit for the non-AST prepass dependency.
r307=A/'artifacts/r307-slice-metadata-inventory'; r307j=load(r307/'llbc-shapes.json'); r307rows=load(r307/'decoded-rows.json')
assert r307j['source']['sha256']==sha(r294) and r307j['projection']['sha256']==sha(A/'artifacts/r298-slice-last-inventory/R299SliceLastProjection.llbc') if (A/'artifacts/r298-slice-last-inventory/R299SliceLastProjection.llbc').exists() else True
assert r307rows['Fun5']['item_meta']['lang_item']=='slice_len_fn'
prepass=r307/'pinned-r289-source/PrePasses.ml'; assert prepass.is_file()
prepass_text=prepass.read_text(); assert 'slice_len_fn' in prepass_text and 'slice_len_call' in prepass_text
# R310 output failure is recorded exactly; no generated output was emitted.
r310=A/'artifacts/r310-slice-last-translation'; r310res=load(r310/'result.json'); r310tr=load(r310/'translation-result.json')
assert r310res['translator_exit_status']==2 and r310res['source_sha256']==sha(r309)
assert r310res['root_emission']['generated_dir_exists'] is False and r310res['root_emission']['translation_json_exists'] is False
assert 'Unhandled Len' in (r310/'translate.log').read_text()
assert r310res['binary_sha256']=='3c741510837e33e0debca5798fb46ae81861ec06d5d561b7975b16f5705e42e9'
# R312 clone/source patch and cached-build provenance, strictly from saved files/metadata.
r312=A/'artifacts/r312-slice-length-tool-candidate'
parent=load(r312/'parent-tree-manifest.json'); pre=load(r312/'candidate-prepatch-tree-manifest.json'); post=load(r312/'candidate-tree-manifest.json')
assert parent==pre
pm={x['path']:x for x in parent if x['kind']=='file'}; qm={x['path']:x for x in post if x['kind']=='file'}
changed=sorted(k for k in pm if k in qm and (pm[k]['sha256'],pm[k]['size'],pm[k]['mode'])!=(qm[k]['sha256'],qm[k]['size'],qm[k]['mode']))
assert changed==['PrePasses.ml']
assert set(pm)==set(qm)
preaudit=load(r312/'prepatch-clone-audit.json'); postaudit=load(r312/'postpatch-tree-audit.json')
assert preaudit['tree_hashes_equal'] and preaudit['shared_regular_file_inodes']==0
assert postaudit['parent_tree_unchanged'] and postaudit['shared_regular_file_inodes_before_or_after']==0
assert postaudit['changed_paths_after_patch']==['PrePasses.ml'] and postaudit['candidate_cached_build_preserved'] and postaudit['candidate_cached_build_file_count']==859
patch=r312/'PrePasses.patch'; parent_src=r312/'PrePasses.parent.ml'; candidate_src=r312/'PrePasses.candidate.ml'
assert sha(parent_src)==load(r312/'build-metrics.json')['parent_PrePasses_sha256']
assert sha(candidate_src)==load(r312/'build-metrics.json')['patched_PrePasses_sha256']
assert sha(patch)==postaudit['patch_sha256']
build=load(r312/'build-result.json'); metrics=load(r312/'build-metrics.json')
binpath=SRC/'r312-slice-length-tool-candidate/aeneas-r312-slice-length-candidate'
assert binpath.is_file() and binpath.stat().st_size==build['binary_size_bytes']
assert sha(binpath)==build['binary_sha256']=='fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f'
assert not (r312/'aeneas-r312-slice-length-candidate').exists()
assert build['build_exit_status']==0 and metrics['exit_status']==0
# Keep the actual CLI measurement distinct from process-in-container RSS and cgroup peaks.
# Systemd slice peak 564,494,336 B is in after reservation snapshot; sampled Docker cgroup 564,445,184 B.
resource={
 'systemd_caps':metrics['caps']['systemd'],'docker_caps':metrics['caps']['docker'],
 'build_process_inside_container':metrics['gnu_time_inside_container'],
 'docker_cli_time':metrics['gnu_time_docker_cli'],
 'docker_cgroup_sample_peak_bytes':metrics['docker_cgroup']['sampled_memory_peak_bytes'],
 'systemd_slice_observed_peak_bytes':int(re.search(r'MemoryPeak=(\d+)',(r312/'build-host-reservation-after.json').read_text()).group(1)),'systemd_slice_swap_peak_bytes':int(re.search(r'MemorySwapPeak=(\d+)',(r312/'build-host-reservation-after.json').read_text()).group(1)),
 'metric_boundary':'Docker CLI RSS is the CLI process, not aggregate build memory; in-container GNU-time RSS and sampled container/systemd cgroup peaks are recorded separately.'}
# R314 completed saved payload; verify target emission against its generated manifest and Lean file.
r314=A/'artifacts/r314-slice-last-translation'; r314res=load(r314/'result.json'); r314tr=load(r314/'translation-result.json')
r314manifest=load(r314/'generated/translation.json'); fs=r314manifest['functions']
assert r314res['translator_exit_status']==0 and r314res['source_sha256']==sha(r309)
assert r314res['binary_sha256']==build['binary_sha256']
assert len(fs)==1 and fs[0]['def_id']==12 and fs[0]['lean_name']=='AspisR314SliceLast.core.slice.Slice.last'
lean=r314/'generated/AspisR314SliceLast/Funs.lean'; text=lean.read_text()
assert sha(lean)==r314res['root_emission']['generated_file_sha256']['generated/AspisR314SliceLast/Funs.lean']
assert 'def core.slice.Slice.last' in text and r314res['root_emission']['root_definition_present']
assert r314res['root_emission']['external_template_axiom_holes']=={'functions':None,'types':None}
assert r314res['root_emission']['template_status'].startswith('Templates were not emitted')
# R316 adapter and failed raw compile are saved evidence only (no rerun).
r316=A/'artifacts/r316-slice-last-raw'; r316binding=load(r316/'binding-audit.json')
oldfail=A/'artifacts/aspis-focus-1790923285872763000.log'; depfail=A/'artifacts/aspis-focus-1790923362572822000.log'
assert 'Usize.sub' in (r316/'rejected-old-subtraction-api/AspisR316SliceLastRaw.lean').read_text()
assert 'Unknown constant `Aeneas.Std.Usize.sub`' in oldfail.read_text()
assert "unknown module prefix 'AspisR316SliceLastRaw'" in depfail.read_text()
assert r316binding['adapter'].startswith('Only generated Usize.sub -> existing UScalar.sub')
assert r316binding['adapted_block_rest_exact'] is True
api_sub=A/'pinned-api/Scalar-Sub.lean'; api_range=A/'pinned-api/RangeIter.lean'
assert 'def UScalar.sub' in api_sub.read_text() and 'Usize.sub' not in api_sub.read_text()
assert 'UScalar.sub_equiv .Usize iter.n (1#usize)' in api_range.read_text()
# Verify the recovered emitter source and the literal LLBC node without assigning semantics.
emitter=A/'pinned-api/emitter'; extract_ml=emitter/'Extract.ml'; extract_base=emitter/'ExtractBase.ml'
assert sha(extract_ml)=='caf4139ec75cdfb721ed44e823e49134927035b1d0655a050d07c06e3fc0cd14'
assert sha(extract_base)=='7209c8454b68c63a838efadb52e9b82ad58a646eabebcfb58c6b4161ee92a0c0'
assert 'Sub (OPanic, _) -> "-"' in (emitter/'Extract.ml.lines589-699.txt').read_text()
assert 'Sub (OWrap, _)' in (emitter/'Extract.ml.lines589-699.txt').read_text()
assert '| Sub (_, ty) -> add_int_name ty ^ "sub"' in (emitter/'ExtractBase.ml.lines935-962.txt').read_text()
fun12=decode(D['fun_decls'][12],srcT)
subnodes=[]
def find_sub(o,path=()):
 if isinstance(o,dict):
  if 'BinaryOp' in o and isinstance(o['BinaryOp'],list) and isinstance(o['BinaryOp'][0],dict) and 'Sub' in o['BinaryOp'][0]: subnodes.append({'path':'/'.join(path),'node':o})
  for k,v in o.items(): find_sub(v,path+(k,))
 elif isinstance(o,list):
  for i,v in enumerate(o): find_sub(v,path+(str(i),))
find_sub(fun12)
assert len(subnodes)==1 and subnodes[0]['node']['BinaryOp'][0]['Sub']=='UB'
assert subnodes[0]['path']=='body/Structured/body/statements/12/kind/Assign/1'
assert subnodes[0]['node']['BinaryOp'][2]['Const']['kind']['Literal']['Scalar']['Unsigned']==['Usize','1']
# R316 compile diagnostics and API evidence are preserved verbatim.
# Confirm archived copies match their saved source folders; R312 binary is the sole excluded file.
copy_checks=[]
for name in ['r307-slice-metadata-inventory','r309-slice-last-with-length-projection','r310-slice-last-translation','r314-slice-last-translation']:
 srcdir=SRC/name; dstdir=A/'artifacts'/name
 sf={p.relative_to(srcdir).as_posix() for p in srcdir.rglob('*') if p.is_file()}
 df={p.relative_to(dstdir).as_posix() for p in dstdir.rglob('*') if p.is_file()}
 assert sf==df,(name,sf-df,df-sf)
 for rel in sf: assert sha(srcdir/rel)==sha(dstdir/rel),(name,rel)
 copy_checks.append({'directory':name,'files_identical':len(sf),'byte_identical':True})
srcdir=SRC/'r312-slice-length-tool-candidate'; dstdir=A/'artifacts/r312-slice-length-tool-candidate'
sf={p.relative_to(srcdir).as_posix() for p in srcdir.rglob('*') if p.is_file()}
df={p.relative_to(dstdir).as_posix() for p in dstdir.rglob('*') if p.is_file()}
excluded='aeneas-r312-slice-length-candidate'; assert sf-df=={excluded} and df==sf-{excluded}
for rel in df: assert sha(srcdir/rel)==sha(dstdir/rel),('r312',rel)
copy_checks.append({'directory':'r312-slice-length-tool-candidate','files_identical':len(df),'byte_identical':True,'excluded_only':excluded})
assert int(re.search(r'MemoryPeak=(\d+)',(r312/'build-host-reservation-after.json').read_text()).group(1))==564494336
# Do not accept or infer execution semantics, axioms, or translation completeness.
report={
 'scope':'Read-only saved-source/tool provenance audit. No build, translator invocation, or Lean compile.',
 'worktree_actual_revision_at_audit':'b268da1cb6878d9b1ab6c2cab79b0592d04dd0ca',
 'R294_to_R309':{'R294_sha256':sha(r294),'R309_sha256':sha(r309),'retained_rows':rowproof,'source_type_fun_global_trait_array_lengths':lengths,'R309_hashcons':{'R294_definitions':len(srcT),'R309_definitions':len(outT),'output_ids_subset':True,'all_emitted_hashcons_values_equal_source':True},'Fun5_slice_len':{'lang_item':'slice_len_fn','opaque_foreign':True,'typed_ast_edge_distinct_from_prepass_lookup':True},'R307_direct_prepass_terms_present':['slice_len_fn','slice_len_call'],'R309_ordered_decls':P['ordered_decls'],'metadata_only_projection_audit_sha256':sha(A/'artifacts/r309-slice-last-with-length-projection/projection-audit.json')},
 'R310':{'translator_exit':r310res['translator_exit_status'],'failure':'Unhandled Len','source_span':'/rustc/library/core/src/slice/mod.rs:282:20-282:24','generated_dir':False,'translation_json':False,**gnu_metrics(r310/'translate.log'),'source_revision':r310res['source_revision_recorded']},
 'R312':{'parent_prepatch_tree_sha256':preaudit['parent_tree_sha256'],'candidate_prepatch_tree_sha256':preaudit['candidate_prepatch_tree_sha256'],'prepatch_byte_identical':preaudit['tree_hashes_equal'],'shared_regular_file_inodes':0,'parent_unchanged':postaudit['parent_tree_unchanged'],'changed_paths':changed,'parent_PrePasses_sha256':sha(parent_src),'patched_PrePasses_sha256':sha(candidate_src),'patch_sha256':sha(patch),'cached_build_preserved':postaudit['candidate_cached_build_preserved'],'cached_build_files':postaudit['candidate_cached_build_file_count'],'binary':{'path':'kept on host; omitted from publication copy','sha256':sha(binpath),'size_bytes':binpath.stat().st_size,'excluded_copy_exists':False},'source_revision':build['source_revision_recorded'],'docker_image':build['docker_image_id'],'metrics':resource},
 'R314':{'translator_exit':r314res['translator_exit_status'],'input_sha256':r314res['source_sha256'],'binary_sha256':r314res['binary_sha256'],'source_revision':r314res['source_revision_recorded'],'emitted_function_entries':len(fs),'root_def_id':fs[0]['def_id'],'root_lean_name':fs[0]['lean_name'],'definition_present':True,'generated_funs_sha256':sha(lean),'no_external_template_files_or_hole_audit_claim':True,'resource_metrics':gnu_metrics(r314/'translate.log'),'axioms':'NOT APPLICABLE: no Lean compile'},
 'R316':{'raw_target_sha256':sha(r316/'AspisR316SliceLastRaw.lean'),'generated_definition_sha256':r316binding['generated_source_sha256'],'adapter':r316binding['adapter'],'adapted_block_rest_exact':r316binding['adapted_block_rest_exact'],'initial_compile':{'exit_status':1,**gnu_metrics(oldfail),'diagnostic':'Unknown constant Aeneas.Std.Usize.sub','log_sha256':sha(oldfail)},'dependent_compile_after_missing_output':{'exit_status':1,**gnu_metrics(depfail),'diagnostic':'unknown module prefix AspisR316SliceLastRaw','log_sha256':sha(depfail)},'pinned_std_scalar_sub_sha256':sha(api_sub),'pinned_std_rangeiter_sha256':sha(api_range),'mechanical_api_observation':'Pinned Std defines UScalar.sub using checked unsigned subtraction and the existing RangeIter proof calls UScalar.sub_equiv at USize width; no Usize.sub declaration was found in the inspected Std/API files. The requested lead-specified identifier adapter is recorded, not semantically assessed.','backend_emission_chain':{'Extract.ml_sha256':sha(extract_ml),'ExtractBase.ml_sha256':sha(extract_base),'Extract.ml_excerpt_lines':'589-699','ExtractBase.ml_excerpt_lines':'935-962','OPanicSub_case':'Lean emits infix subtraction notation -','OWrapSub_case':'Lean emits Std.<IntName>.wrapping_sub','other_subtraction_modes':'delegate to named_binop_name','named_sub_emission':'Lean add_int_name returns int_name ty plus a dot; Sub case appends sub','decoded_Fun12_subtraction_node':subnodes[0],'actual_LLBC_mode_tag':subnodes[0]['node']['BinaryOp'][0]['Sub'],'node_excerpt_sha256':sha(emitter/'fun12-subtraction-node.json'),'source_probe_status':'Earlier no-match search preserved as historical; exact source path now located.'}},
 'interpretive_boundary':'The R289 slice_len_fn prepass dependency was restored in the R309 projection; the saved evidence preserves unchanged source LLBC rows. R310 failed Unhandled Len with no output. R312 is a saved isolated one-file PrePasses candidate build only. R314 emitted a Slice.last declaration from the candidate binary but no Lean compilation or template completion. R316 raw compilation first failed on Usize.sub and the dependent draft then failed because the prior raw module had no output. Lead-specified UScalar.sub identifier adapter is documented; this audit does not assess its semantic adequacy. The exact pinned emitter chain is now recorded from Extract.ml and ExtractBase.ml and paired with the decoded R309 Fun12 node; this establishes emitted naming only, not arbitrary-input operation equivalence. Source semantics and translation soundness remain lead decisions; no source-execution or release gate is asserted.',
 'archive_copy_checks':copy_checks,
 'excluded_large_file':{'path':'r312-slice-length-tool-candidate/aeneas-r312-slice-length-candidate','size_bytes':binpath.stat().st_size,'sha256':sha(binpath),'reason':'49 MB binary remains on the host; its hash and build receipt are included.'}}
(A/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'R294_to_R309_rows':len(rowproof),'R312_changed_paths':changed,'R312_binary_sha256':sha(binpath),'R314_root_emitted':fs[0]['lean_name'],'report_sha256':sha(A/'audit.json')},indent=2))
