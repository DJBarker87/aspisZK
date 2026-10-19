#!/usr/bin/env python3
"""Audit full actual preparation rho dataflow and initial-source consuming bridge."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run([sys.executable,str(here/'prepare-rho-prepared-source.py'),'--check'],check=True,capture_output=True)
targets={'AspisR1RhoPrepared/Types':'rho-prepared-types-a','AspisR1RhoPrepared/FunsExternal':'rho-prepared-externals-a','CuSavingsRhoPreparedScalar':'rho-prepared-scalar-proof-a','AspisR1RhoPrepared/Funs':'rho-prepared-funs-b','CuSavingsRhoPrepared':'rho-prepared-proof-d','CuSavingsRhoInitialPower':'rho-initial-power-proof-a'}
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
# Read accepted predecessor receipts; do not repeat unchanged proof targets.
for report in ['RHO-POWER-TAIL.json','RHO-ACCUMULATOR-NEW.json','RHO-CANONICAL-INPUTS.json']:
 for module,pin in json.loads((ev/report).read_text())['successes'].items():
  old=json.loads((ev/pin['attempt']/'receipt.json').read_text());assert old['exit_status']==0
  source=area/'lean'/(module+'.lean')
  if 'source_repository_path' in pin:source=repo/pin['source_repository_path']
  assert sha(source.read_bytes())==old['source_sha256']
  objects[module.replace('/','.')]=old['object_sha256']
for module,r in receipts.items():
 for item in r['direct_imports']:
  if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
ext=(area/'lean/AspisR1RhoPrepared/FunsExternal.lean').read_text()
assert 'let (q,after) ← AspisR1CuRho.transcript.Transcript.scalar_k D self row payload' in ext
assert '.ok (fromRhoSource q,after)' in ext
assert not re.search(r'(?m)^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b',ext)
common=ext.split('class PreparedCommon where',1)[1].split('abbrev aspis_core.field.WideExact.to_le_bytes',1)[0]
assert 'scalarK' not in common and 'Prop' not in common
for p in (area/'lean/AspisR1RhoPrepared').glob('*.lean'):assert not re.search(rb'(?m)^\s*(axiom|opaque)\s|\b(sorry|admit)\b',p.read_bytes()),p
emission_path=ev/'cu-gamma-aeneas-prepared-b/receipt.json';emission=json.loads(emission_path.read_text());assert emission['exit_status']==0
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='ACTUAL_PREPARED_RHO_DATAFLOW_AND_INITIAL_POWER_BRIDGE_CHECKED',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,
 reused_source_emission=dict(receipt_sha256=sha(emission_path.read_bytes()),source_revision=emission['source_revision'],features=emission['features'],command=emission['command'],exit=0,wall_seconds=emission['wall_seconds'],peak_rss_kib=emission['peak_rss_kib'],process_swaps=emission['process_swaps'],note='Existing exact source emission reused; no new producer/SBF/runtime run.'),
 covered=['Whole actual Prepared.new is byte-identical in exact candidate12, parent and frozen source, and equals the earlier emitted method after recorded declaration-only rename.',
 'The complete raw emitted method is selected unchanged; exact shared carriers/constants/folds reused. No smaller gamma optimization equivalence is asserted or worked on.',
 'scalar_k is actual checked source with invertible coordinate-only QM31 transport. Transcript and Digest32 source carriers are shared identically.',
 'Other common computations are universally quantified computational fields without any success or canonicality law. scalar_k is not one of those arbitrary fields.',
 'Whole successful actual preparation yields canonical stored rho and exact dataflow witness to the actual scalar_k return and final transcript state, in both fold branches. No child-success or rho-canonicality premise.',
 'Source initial-power consuming bridge combines actual Prepared.new and Accumulator.new successes to derive source power-tail success, canonical output, counter1 and weights/RHS frames without input canonicality/counter assumptions.'],
 remaining=['Actual intervening complete query/coefficient/RHS context composition; initial bridge does not skip or replace that requirement.',
 'Full resume caller/weight traversal binding and actual reserve frame/sufficient-resource source connection.',
 'Original optimized Option nested-borrow source binding and final tx1_finish/tx2/tx2_authenticated observable equivalence.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,print_axioms='N/A source/receipt audit; exact per-target declarations included'))
(ev/'RHO-PREPARED.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
