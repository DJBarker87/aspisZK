#!/usr/bin/env python3
"""Audit actual constructor success/outcome, heap binding and enum-name repair."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-rho-accumulator-new.py','emit-rho-accumulator-new.py','extract-rho-resume-weights.py']:subprocess.run([sys.executable,str(here/script),'--check'],check=True,capture_output=True)
subprocess.run([sys.executable,str(here/'check-rho-power-tail.py')],check=True,capture_output=True)
targets={'AspisR1RhoAccumulatorNew/Types':'rho-accumulator-new-types-c','AspisR1RhoAccumulatorNew/FunsExternal':'rho-accumulator-new-externals-c','AspisR1RhoAccumulatorNew/Funs':'rho-accumulator-new-funs-c','CuSavingsRhoAccumulatorNew':'rho-accumulator-new-proof-c','CuSavingsRhoVariantRegistration':'rho-variant-fixed-registration-a'}
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
power=json.loads((ev/'RHO-POWER-TAIL.json').read_text())
for module,r in power['successes'].items():objects[module.replace('/','.')]=r['object_sha256']
heap=json.loads((ev/'rho-heap-funs-a/receipt.json').read_text());objects['AspisR1RhoHeap.Funs']=heap['object_sha256']
heap_proof=json.loads((ev/'rho-heap-proof-b/receipt.json').read_text());objects['CuSavingsRhoHeap']=heap_proof['object_sha256']
for module,r in receipts.items():
 for item in r['direct_imports']:
  if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
old=ev/'rho-variant-original-registration-a';new=ev/'rho-variant-fixed-registration-a';oldr=json.loads((old/'receipt.json').read_text());assert oldr['exit_status']==0
oldlog=(old/'stdout.log').read_text();newlog=(new/'stdout.log').read_text()
assert oldlog.split('@[implicit_reducible]')[0]==newlog.split('@[implicit_reducible]')[0]
assert 'sorryAx' not in oldlog and 'error:' not in oldlog
oldsource=(old/'source.lean').read_text();newsource=(new/'source.lean').read_text()
assert oldsource.replace('#print instDiscriminantVariantIsize','#print AspisR1RhoPowerTail.transport.Variant.instDiscriminant')==newsource
oldtype=json.loads((ev/'rho-power-tail-types-a/receipt.json').read_text());newtype=json.loads((ev/'rho-power-tail-types-b/receipt.json').read_text())
assert next(i['sha256'] for i in oldr['direct_imports'] if i['module']=='AspisR1RhoPowerTail.Types')==oldtype['object_sha256']
assert next(i['sha256'] for i in receipts['CuSavingsRhoVariantRegistration']['direct_imports'] if i['module']=='AspisR1RhoPowerTail.Types')==newtype['object_sha256']
source_runs={}
for prefix in ['rho-accumulator-new-charon-a','rho-accumulator-new-aeneas-a','rho-resume-weights-charon-a','rho-resume-weights-aeneas-a','rho-resume-weights-charon-b','rho-resume-weights-aeneas-b']:
 p=ev/prefix/'receipt.json';r=json.loads(p.read_text());expected=2 if 'resume-weights-aeneas' in prefix else 0;assert r['exit_status']==expected
 kit=here/'rho-accumulator-new-input' if 'accumulator-new' in prefix else (ev/'rho-resume-weights-aeneas-a/input' if prefix.endswith('-a') else here/'rho-resume-weights-input')
 assert r['source_pins_sha256']==sha((kit/'source-pins.json').read_bytes())
 source_runs[prefix]=dict(receipt_sha256=sha(p.read_bytes()),command=r['command'],source_revision=r['source_revision'],features=r['features'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'])
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='ACTUAL_ACCUMULATOR_NEW_SUCCESS_INVARIANTS_CHECKED_RESUME_CONTEXT_OPEN',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,source_extraction=source_runs,
 covered=['Complete unchanged Accumulator.new, constants, final_len and folds extracted from exact candidate, parent and frozen production source; all identical.',
 'Exact heap helper bound with the existing universally quantified reserve boundary. No successful-allocation, reserve-frame or initialized-weight canonicality assumption supplied.',
 'Every successful actual constructor output has next=0, canonical power=ONE, RHS=ZERO, actual 256/64 coefficient length and length≤256.',
 'Full constructor outcome retains reserve/heap errors, runtime failures and divergence; no child success premise.',
 'Raw source function bodies unchanged. The enum registration collision is repaired only by a qualified instance name; original/new 0/1/2 reader functions printed identically, constructor facts checked separately against respective exact objects.'],
 remaining=['Canonical zero weights need the actual reserve-frame/source resource connection; length alone does not establish it.',
 'Prepared.rho and resume output dataflow through actual callers; full source resume weight traversal binding.',
 'Original optimized coefficient Option nested-borrow source binding, sufficient-resource conditions and final transaction observable contexts.'],
 rejected_resume_translation=['Direct factored loop with borrowed Reader: Nested borrows not supported, InterpAbs.ml:168.',
 'Refactoring the helper to retain both original local owners weights and Reader: InterpBorrowsCore.ml:984. Neither failed emission is admitted; no further flag variants are justified.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,print_axioms='N/A source/receipt audit; exact per-target axiom lists included'))
(ev/'RHO-ACCUMULATOR-NEW.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
