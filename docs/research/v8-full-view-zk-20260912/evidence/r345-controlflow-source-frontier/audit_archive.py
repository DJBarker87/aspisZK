from pathlib import Path
import hashlib, json, shutil, re
repo=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
root=repo/'.r21-scratch/r345-controlflow-source-frontier'
sources=['r334-controlflow-source-projection','r338-controlflow-source-translation','r339-controlflow-output-source-projection','r343-controlflow-output-source-translation']
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
archive=root/'archive'
files=[]; tree_checks={}
for name in sources:
 src=repo/'.r21-scratch'/name; dst=archive/name
 sf={p.relative_to(src).as_posix() for p in src.rglob('*') if p.is_file()}
 df={p.relative_to(dst).as_posix() for p in dst.rglob('*') if p.is_file()}
 ok=(sf==df)
 diffs=[]
 for rel in sorted(sf|df):
  if rel not in sf or rel not in df:
   diffs.append({'path':rel,'source_exists':rel in sf,'archive_exists':rel in df}); continue
  sh,dh=digest(src/rel),digest(dst/rel)
  same=(src/rel).read_bytes()==(dst/rel).read_bytes()
  if sh!=dh or not same: diffs.append({'path':rel,'source_sha256':sh,'archive_sha256':dh,'byte_equal':same})
  files.append({'tree':name,'path':rel,'bytes':(src/rel).stat().st_size,'sha256':sh,'archive_byte_equal':same})
 tree_checks[name]={'source_file_count':len(sf),'archive_file_count':len(df),'identical_relative_paths':sf==df,'all_bytes_equal':ok and not diffs,'differences':diffs}
# Projection claims from exact retained audit files.
proj=[]
for name in [sources[0],sources[2]]:
 d=repo/'.r21-scratch'/name; m=json.loads((d/'manifest.json').read_text()); a=json.loads((d/'projection-audit.json').read_text()); sums={}
 for line in (d/'SHA256SUMS').read_text().splitlines():
  h,p=line.split('  ',1); p=Path(p); p=p.relative_to(repo) if p.is_absolute() else p; sums[str(p)]=h
 llbc=d/m.get('projection_file',m.get('projection'))
 inp=d/m.get('source_file',m.get('input'))
 if not inp.exists(): inp=d/'input/R327PrivateBatchSourceTryFold.llbc'
 proj.append({'name':name,'manifest':m,'projection_audit_facts':{k:a.get(k) for k in ['input_sha256','output_sha256','all_decoded_reachable_rows_equal_source','all_output_hashcons_values_equal_original','missing_references','unknown_typed_reference_shapes','source_rows_edited','only_changed_translated_paths','selected_body_loop_and_erased_region_census','closure_counts','typed_reference_occurrence_count','reachable_declaration_count','root_rows_exact_identity_verified_against_audit','all_decoded_reachable_rows_equal_source','all_output_hashcons_values_equal_original','missing_references','unknown_typed_reference_shapes','only_changed_translated_paths']},'projection_file_actual_sha256':digest(llbc),'input_actual_sha256':digest(inp),'source_internal_sums_valid':all(digest(repo/p)==h for p,h in sums.items() if (repo/p).exists())})
trans=[]
for name in [sources[1],sources[3]]:
 d=repo/'.r21-scratch'/name; c=json.loads((d/'command.json').read_text()); l=json.loads((d/'launch.json').read_text()); r=json.loads((d/'result.json').read_text()); log=(d/'translate.log').read_text(); host=json.loads((d/'host-reservation-before.json').read_text())
 rgx={'exit_status_2':r['exit_status']==2 and 'Exit status: 2' in log,'no_generated_output':r.get('generated_files')=={},'no_Lean_compile':r.get('Lean_compiled') is False and r.get('print_axioms')=='N/A; translation only','metrics_match_declared':('r338' in name.lower() and '0:00.18' in log and 'Maximum resident set size (kbytes): 54032' in log and 'Swaps: 0' in log) or ('r343' in name.lower() and '0:00.21' in log and 'Maximum resident set size (kbytes): 55440' in log and 'Swaps: 0' in log),'capped_launch':all(x in l['argv'] for x in ['MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128']),'reservation_at_least_24GiB':host['available_kib']>=24*1024*1024,'projection_hash_matches_command':hashlib.sha256((d/Path(c['command'][-1]).name).read_bytes()).hexdigest()==c['source_sha256'],'binary_sha_matches_launch_receipt':c['binary_sha256']==l.get('binary_sha256',c['binary_sha256'])}
 trans.append({'name':name,'command':c,'launch_resource_caps':{k:host['caps'].get(k) for k in ['MemoryHigh','MemoryMax','MemorySwapMax','TasksMax']},'host_available_kib':host['available_kib'],'result':r,'metrics_and_outcome_checks':rgx,'log_sha256':digest(d/'translate.log'),'launch_sha256':digest(d/'launch.json'),'runner_sha256':l.get('runner_sha256'),'binary_sha256':c.get('binary_sha256'),'source_revision':c.get('source_revision')})
# Distinct failure points are extracted literally; strip the log's ANSI color codes first.
r338log=(repo/'.r21-scratch/r338-controlflow-source-translation/translate.log').read_text(); r343log=(repo/'.r21-scratch/r343-controlflow-output-source-translation/translate.log').read_text(); ansi=re.compile(r'\x1b\[[0-9;]*m'); r338clean=ansi.sub('',r338log); r343clean=ansi.sub('',r343log)
failure={'r338_enum_expansion':'Not allowed to expand enumerations with several variants' in r338clean and 'Source: \'/rustc/library/core/src/ops/control_flow.rs\', lines 131:31-131:32' in r338clean and 'Fun40' in json.loads((repo/'.r21-scratch/r334-controlflow-source-projection/manifest.json').read_text())['roots'][2], 'r343_name_collision':'core.ops.control_flow.ControlFlow' in r343clean and 'ControlFlow::<(), ()>' in r343clean and 'ControlFlow::<(), core::convert::Infallible>' in r343clean}
report={'archive':'recursive scratch-only copies of R334/R338/R339/R343','read_only':True,'no_builds_or_reruns':True,'trees':tree_checks,'files':files,'projections':proj,'translations':trans,'failure_checks':failure,'boundary':'R334/R339 are metadata projections. Their audits report unchanged decoded reachable source rows and hash-cons values, no source/body/signature/type/region/lang-item edits, no missing recognized references, and zero unknown recognized typed-reference shapes. R338/R343 are unsuccessful Aeneas translations with no generated output and no Lean axioms to report. These artifacts isolate current translation/compiler frontiers only; they do not prove source semantics, source guards, fold/extend behavior, or complete batch execution. All negative/incomplete projection history is included in the recursive copies.','overall':'PASS' if all(v['all_bytes_equal'] for v in tree_checks.values()) and all(p['source_internal_sums_valid'] and p['projection_file_actual_sha256']==p['manifest'].get('projection_sha256',p['manifest'].get('projection_sha256',p['manifest'].get('projection_sha256',''))) for p in proj) and all(all(t['metrics_and_outcome_checks'].values()) for t in trans) and all(failure.values()) else 'REVIEW'}
(root/'archive-inventory.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'overall':report['overall'],'trees':tree_checks,'projection_source_rows_and_checksums':[(p['name'],p['source_internal_sums_valid'],p['projection_file_actual_sha256']) for p in proj],'translations':[(x['name'],x['metrics_and_outcome_checks']) for x in trans],'failure_checks':failure},indent=2))
