#!/usr/bin/env python3
"""Audit source suffix, exact arithmetic binding and coherent focused Lean receipts."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-rho-power-tail.py','emit-rho-power-tail.py']:subprocess.run([sys.executable,str(here/script),'--check'],check=True,capture_output=True)
targets={'ExtractedCurrentQM31Mul':'rho-power-mul-repin-a','AspisR1RhoPowerTail/Types':'rho-power-tail-types-a','AspisR1RhoPowerTail/FunsExternal':'rho-power-tail-externals-a','AspisR1RhoPowerTail/Funs':'rho-power-tail-funs-a','CuSavingsRhoPowerTail':'rho-power-tail-proof-b'}
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
old=json.loads((area/'evidence/current-qm31-arithmetic-20261015/lean-attempts/qm31-mul-b/qm31-mul-b.receipt.json').read_text());assert results['ExtractedCurrentQM31Mul']['source_sha256']==old['source_sha256']
source_runs={}
for attempt in ['rho-power-tail-charon-b','rho-power-tail-aeneas-b']:
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 assert r['source_pins_sha256']==sha((here/'rho-power-tail-input/source-pins.json').read_bytes())
 source_runs[attempt]=dict(source_features=json.loads((here/'rho-power-tail-input/source-pins.json').read_text())['features'],receipt_sha256=sha(p.read_bytes()),command=r['command'],source_revision=r['source_revision'],features=r['features'],exit=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'])
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_POWER_COUNTER_SUFFIX_CHECKED_CALLER_COMPOSITION_OPEN',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,source_extraction=source_runs,
 covered=['Exact byte-identical power/counter suffix from parent and candidate, complete original Prepared/Accumulator carriers, whole emitted tail unchanged.',
 'External mul binds to the byte-identical existing source QM31 multiplication through invertible coordinate transport, without a template axiom.',
 'Canonical power and rho plus entry next<22 imply actual suffix success, canonical resulting power, exact modular product, next+1≤22 and unchanged weights/rhs.',
 'Unconditional source outcome retains mul/add errors and divergence. No child-call success premise.',
 'Existing QM multiplication proof re-pinned in Lean4.32 because prior available source receipt was Lean4.31. New object equals already consumed object; no dependent rerun needed.'],
 remaining=['Derive initial/resumed power and Prepared.rho canonicality and range bounds through actual callers.',
 'Compose coefficient loop, RHS prefix, source power tail and transaction contexts.',
 'Original optimized Option reborrow source binding and sufficient-resource allocation connection.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,print_axioms='N/A receipt/source audit; per-target declarations included'))
(ev/'RHO-POWER-TAIL.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
