"""Final read-only artifact/receipt validation; no Lean invocation."""
from pathlib import Path
import json,subprocess,hashlib,collections,re
E=Path(__file__).resolve().parent;R=E.parents[1];g=json.loads((E/'RPz3_source-plan.json').read_text());f=json.loads((E/'RPz3_frontier.json').read_text());a=json.loads((E/'RPz3_axiom-audit.json').read_text());inv=json.loads((E/'RPz3_final-object-inventory.json').read_text());reuse=json.loads((E/'RPz3_reuse.json').read_text());rs=[json.loads(p.read_text()) for p in sorted(E.glob('RPz3_*/receipt.json'))];green={}
for m,rel in reuse['receipts'].items():
 if reuse['state'][m]=='passed':green[m]=json.loads((R/rel).read_text())
for r in rs:
 if r['exit_status']==0 and not r['module'].startswith('RPz3_Audit'):green[r['module']]=r
edges=[]
for r in list(green.values())+[r for r in rs if r['module'].startswith('RPz3_Audit') and r['exit_status']==0]:
 for n,pin in r['deps_fingerprint']['selected_objects'].items():edges.append({'consumer':r['module'],'dependency':n,**pin})
paths=sorted({x['path'] for x in edges})
payload='''import json,hashlib,subprocess
from pathlib import Path
paths=json.loads(%r);actual={}
for s in paths:
 p=Path(s);actual[s]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} if p.is_file() else None
live=[]
for line in subprocess.check_output(['ps','-eo','pid,comm,args'],text=True).splitlines()[1:]:
 parts=line.split(None,2)
 if len(parts)==3 and parts[1] in ['python3','lean','lake'] and 'RPz3_' in parts[2]:live.append(line)
print(json.dumps({'objects':actual,'live_job_processes':live}))
'''%json.dumps(paths)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=payload,text=True,capture_output=True);assert r.returncode==0,r.stderr
host=json.loads(r.stdout);mismatch=[x for x in edges if host['objects'][x['path']]!={k:x[k] for k in ['sha256','bytes']}];errors=[]
if mismatch:errors.append('stale direct dependency object')
if host['live_job_processes']:errors.append('live job compiler/runner')
if f['verification_errors'] or f['unchanged_input_retries']:errors.append('receipt/input consistency')
if a['audit_completion_errors'] or a['source_import_header_mismatches'] or a['passed_modules_missing_audit'] or a['duplicate_owner_name_pairs']:errors.append('audit coverage/header consistency')
if a['declaration_queries']!=a['raw_print_results']:errors.append('raw axiom count')
if len(green)!=1378 or f['ready_unattempted']:errors.append('source frontier')
if not f['all_attempt_numbers_contiguous'] or len(rs)!=591:errors.append('attempt numbering')
if inv['trusted_artifacts_missing'] or inv['default_lake_object_directory_exists']:errors.append('trusted artifacts/default search path')
expected_drift='/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py'
if len(inv['trusted_artifacts_changed'])!=1 or inv['trusted_artifacts_changed'][0]['path']!=expected_drift or inv['trusted_artifacts_changed'][0]['after']['sha256']!='195657d75fd2a290c236f078fca4247929f214d4f693532ae1fb4d5edc34d893':errors.append('unexpected trusted drift')
old=json.loads((E/'RPz3_reuse-check.json').read_text())['objects'];old_bad=[k for k,v in old.items() if inv['fresh_repository_objects'].get(k)!=v]
if old_bad:errors.append('inherited object changed')
source_bad=[m for m in g['order'] if hashlib.sha256((R/g['modules'][m]['source']).read_bytes()).hexdigest()!=g['modules'][m]['sha256']]
if source_bad:errors.append('selected source changed')
prefixes=['AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug','AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug'];outside=[d for d in a['nonstandard_queries'] if not any(d['name']==p or d['name'].startswith(p+'.') for p in prefixes)]
if outside:errors.append('nonstandard dependency outside formatter families')
paths_changed=subprocess.check_output(['git','diff','--name-only','acf38be800b73709426019baf85a3db32a40196b','HEAD'],text=True).splitlines()
if any(not p.startswith('evidence/replay-dry4-20261026/RPz3_') for p in paths_changed):errors.append('out-of-prefix committed path')
lean_bad=[str(p) for p in E.glob('RPz3_*.lean') if re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text())]
if lean_bad:errors.append('forbidden new query source token')
out={'errors':errors,'attempts':len(rs),'source_attempts':f['source_attempts'],'source_passed':f['source_passed'],'audit_attempts':f['audit_attempts'],'audit_passed':f['audit_passed'],'passed_attempts_total':sum(r['exit_status']==0 for r in rs),'failed_attempts_total':sum(r['exit_status']!=0 for r in rs),'green_contexts':len(green),'verified_direct_edges':len(edges),'verified_unique_dependency_paths':len(paths),'dependency_mismatches':mismatch,'source_hash_errors':source_bad,'inherited_object_changes':old_bad,'source_repeated_targets':f['repeated_targets'],'unchanged_input_retries':f['unchanged_input_retries'],'axiom_query_records':a['declaration_queries'],'distinct_global_names':a['distinct_global_names'],'raw_print_results':a['raw_print_results'],'repeated_global_names':a['repeated_global_names'],'nonstandard_query_count':len(a['nonstandard_queries']),'nonstandard_axiom_count':len(a['nonstandard_axioms']),'nonstandard_outside_formatter_families':outside,'formatter_matcher_consumers':a['parser_formatter_external_consumers'],'standard_only_gate_all_declarations':False,'top_reached':False,'top_axioms_and_external_reachability':'UNKNOWN; fresh top not reached','wall_seconds_sum':f['wall_seconds_sum'],'max_peak_rss_kib':f['max_peak_rss_kib'],'swap_sum':f['swaps_sum'],'live_job_processes':host['live_job_processes'],'trusted_artifacts_present':inv['trusted_artifacts_checked'],'trusted_artifact_drift':inv['trusted_artifacts_changed'],'lean_budget_used':591,'lean_budget_limit':1500,'kani_runs':0,'ledger_delta':{'T':0,'P':0,'G':0,'C':0},'non_vacuity':'No fresh joint inhabitant; historical conditional witnesses retained','new_query_token_errors':lean_bad,'scope':'Partial source import closure; no release or complete top proof claim.'}
(E/'RPz3_final-verification.json').write_text(json.dumps(out,indent=2)+'\n');(E/'RPz3_terminal-host-check.json').write_text(json.dumps({'live_job_processes':host['live_job_processes']},indent=2)+'\n');print({k:out[k] for k in ['errors','attempts','green_contexts','verified_direct_edges','verified_unique_dependency_paths','axiom_query_records','nonstandard_query_count','wall_seconds_sum','max_peak_rss_kib']})
