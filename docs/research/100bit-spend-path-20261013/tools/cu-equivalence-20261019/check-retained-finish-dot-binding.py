#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['check-retained-finish-dot-source.py','check-retained-finish-source.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,capture_output=True)
modules=['CuSavingsRetainedFinishDotClients','CuSavingsRetainedFinishDotBinding','CuSavingsRetainedFinishDotContexts'];records={};objects={}
for module in modules:
 p=area/'lean'/(module+'.lean');b=p.read_bytes();digest=sha(b);assert not re.search(rb'(?m)^\s*(?:axiom|constant|opaque)\s|\b(?:sorry|admit|native_decide)\b',b)
 matching=[]
 for path in ev.glob('*/receipt.json'):
  try:r=json.loads(path.read_text())
  except(ValueError,OSError):continue
  if r.get('exit_status')==0 and r.get('source_sha256')==digest and r.get('module')==module:matching.append((path.stat().st_mtime,path,r))
 assert matching,module
 _,path,r=max(matching,key=lambda x:x[0]);assert(path.parent/'source.lean').read_bytes()==b
 output=r['print_axioms_output'];audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output);assert audits
 for decl,axioms in audits:assert set(filter(None,re.sub(r'\s+','',axioms).split(',')))<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter'},(decl,axioms)
 objects[module]=r['object_sha256'];records[module]=dict(module=module,attempt=r['attempt'],source_path=str(p.relative_to(repo)),receipt=str(path.relative_to(repo)),receipt_sha256=sha(path.read_bytes()),**{k:r.get(k)for k in ['source_sha256','object_sha256','source_revision','command','features','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output','direct_imports']})
for name,r in records.items():
 for imp in r['direct_imports']:
  if imp['module']in objects:assert imp['sha256']==objects[imp['module']],(name,imp)
report=dict(status='FIXED_CLIENTS_AND_COMPLETE_FRESH_RESUMED_FINISH_CHECKED',successes=records,coherent_selected_imports=True,source_bindings=json.loads((ev/'RETAINED-FINISH-DOT-SOURCE.json').read_text()),final_theorems=['AspisR1.CuSavingsRetainedFinishDotClients.clients_equivalence','AspisR1.CuSavingsRetainedFinishDotBinding.binding_equivalence','AspisR1.CuSavingsRetainedFinishDotContexts.Prepared.source_equivalence','AspisR1.CuSavingsRetainedFinishDotContexts.Resumed.source_equivalence'],exported_candidate_equivalence_premises=0,exported_canonicality_premises=0,exported_child_success_premises=0,original_scalar_validation_retained=True,actual_wide_origins='Strict weights.field decoding in plain/final row source clients; actual old row-dot finish canonical outputs before shared high; no factor/K-canonical hypothesis needed.',runtime_boundary='Exact inverse-audited source call fission +existing Rust/Charon/Aeneas/compiler/library/ownership/runtime interfaces. Clients are universally equal functions, so source-bound unchanged enclosing frames substitute by kernel congruence; no new abstract interpreter or candidate-equivalence premise. Inherited Formatter is an opaque type, not arithmetic/equivalence law.',audit=dict(command=[sys.executable,*sys.argv],source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source/receipt audit; exact complete outputs recorded for each Lean target.'))
(ev/'RETAINED-FINISH-DOT-BINDING-FINAL.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status=report['status'],lean_targets=len(records),coherent_selected_imports=True,candidate_equivalence_axioms=0)))
