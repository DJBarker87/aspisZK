#!/usr/bin/env python3
"""Audit source-derived Option leaves and proof receipts; never certify caller lowering."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run([sys.executable,str(here/'check-rho-option-source.py')],check=True,capture_output=True)
targets={'AspisR1RhoOptionLeaves/Types':'rho-option-leaf-types-b','AspisR1RhoOptionLeaves/Funs':'rho-option-leaf-funs-a','AspisR1RhoReferenceDeref/Types':'rho-reference-deref-types-a','AspisR1RhoReferenceDeref/Funs':'rho-reference-deref-funs-a','CuSavingsRhoOptionLoans':'rho-option-loans-proof-c'}
results={};objects={};receipts={}
for module,attempt in targets.items():
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 b=(area/'lean'/(module+'.lean')).read_bytes();assert sha(b)==r['source_sha256'];assert b==(ev/attempt/'source.lean').read_bytes()
 log=(ev/attempt/'stdout.log').read_text();assert log==r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 decls=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert decls
 for n,a in decls:assert set(filter(None,re.sub(r'\s+','',a).split(',')))<={'propext','Quot.sound','Classical.choice'},(n,a)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]=dict(attempt=attempt,source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],receipt_sha256=sha(p.read_bytes()),source_revision=r['source_revision'],features=r['features'],command=r['command'],exit=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],cgroup_swap_bytes=r['cgroup_swap_bytes'],axiom_declarations=[dict(name=n,axioms=list(filter(None,re.sub(r'\s+','',a).split(',')))) for n,a in decls])
for module,r in receipts.items():
 for item in r['direct_imports']:
  if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
failures={}
for prefix in ['rho-coefficients-consumed','rho-coefficients-deref','rho-local-option','rho-option-branch']:
 attempts={}
 for kind in ['charon','aeneas']:
  attempt=prefix+'-'+kind+'-a';p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==(0 if kind=='charon' else 2)
  attempts[kind]=dict(attempt=attempt,receipt_sha256=sha(p.read_bytes()),exit=r['exit_status'],command=r['command'],revision=r['source_revision'],features=r['features'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],print_axioms='N/A source extraction, no Lean result')
 failures[prefix]=attempts
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_LEAF_WRITEBACK_PROOFS_CHECKED_NESTED_CALLER_LOWERING_OPEN',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,frontend_diagnostics=failures,
 scope=['Installed std as_mut/map/DerefMut identity bodies checked against local generic extraction inputs after explicit receiver/const declaration transport.',
 'Generic as_mut and map emitted unchanged with original producer; identity reference method emitted unchanged. No opaque templates imported.',
 'Checked Option discriminant-preserving restore, both identity reborrow handbacks, complete map outcomes and packaged-loan update behavior.',
 'These component theorems do not establish original as_deref_mut nested-borrow source lowering. No hand-written compatible API has been admitted as that lowering.'],
 blockers=['Original optimized std dependency MIR copies mutable borrows in deref_mut and as_mut; original producer rejects these.',
 'Local exact std helper composition fails nested mutable type backward-level computation.',
 'Direct branch-normalized diagnostic also fails nested-loan handback translation; it is not accepted as source equivalent or imported.'],
 remaining=['Bind original optimized coefficient loop Option reborrow to a source-justified loan lowering.',
 'Actual Prepared/resume/accumulate caller canonicality, length, count and power invariants.',
 'Allocation sufficient-resource connection and actual transaction observable-context equivalence.'],
 receipt_note='Some source-only diagnostic plans inherit an unrelated old scope string from the runner template. Their expected_work, exact command and source-pins identify the diagnostic; this report does not claim that inherited decoder scope.',
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,print_axioms='N/A receipt audit; exact per-target axiom lists included'))
(ev/'RHO-OPTION-LOANS.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
