#!/usr/bin/env python3
"""Check actual source resume loop, exact bindings, repaired producer, and receipts."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for n in ['extract-rho-resume-weights.py','extract-rho-resume-inlined.py','emit-rho-resume-source.py']:
 subprocess.run([sys.executable,str(tool/n),'--check'],check=True,capture_output=True)
producer=tool/'rho-original-producer-repair';provenance=json.loads((producer/'provenance.json').read_text())
assert provenance['base_binary_sha256']=='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
assert sha((producer/'producer.patch').read_bytes())==provenance['patch_sha256']
assert sha((producer/'source-pins.json').read_bytes())==provenance['source_files_manifest_sha256']
assert set(provenance['changed'])=={'src/interp/InterpExpressions.ml','src/symbolic/SymbolicToPureValues.ml','src/interp/InterpReduceCollapse.ml'}
plan=json.loads((ev/'rho-resume-inlined-aeneas-c-plan.json').read_text());assert plan['frontend_binary_sha256']==provenance['repaired_binary_sha256'];assert '-checks' in plan['command']
fmt=json.loads((ev/'rho-reader-fmt-boundary.json').read_text());fmt_object=next(x for x in fmt if x.get('module')=='Aeneas/Std/Core/Fmt.olean');fmt_source=next(x for x in fmt if x.get('source','').endswith('/Core/Fmt.lean'))
assert fmt_object['sha256']=='7c17a7af2952203781321279f0c569410d27bd9f1233fa3f5d1ec6f67a07f068'
assert fmt_source['sha256']=='26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce'
assert sha(fmt_source['text'].encode())==fmt_source['sha256'];assert 'axiom core.fmt.Formatter : Type' in fmt_source['text']
targets={'AspisR1RhoResumeInlined/Types':'rho-resume-inlined-types-a','AspisR1RhoResumeInlined/FunsExternal':'rho-resume-inlined-externals-b','AspisR1RhoResumeInlined/Funs':'rho-resume-inlined-funs-b','CuSavingsRhoResumeLoans':'rho-resume-loans-a','CuSavingsRhoResumeCanonical':'rho-resume-canonical-e'}
results={};objects={};receipts={}
for module,attempt in targets.items():
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 src=(area/'lean'/(module+'.lean')).read_bytes();assert sha(src)==r['source_sha256'];assert src==(ev/attempt/'source.lean').read_bytes()
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 ds=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert ds
 allowed={'propext','Classical.choice','Quot.sound'}
 if module in ['AspisR1RhoResumeInlined/Funs','CuSavingsRhoResumeCanonical']:allowed.add('core.fmt.Formatter')
 for n,a in ds:assert set(filter(None,re.sub(r'\s+','',a).split(',')))<=allowed,(n,a)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']};results[module].update(attempt=attempt,receipt_sha256=sha(p.read_bytes()))
for module,r in receipts.items():
 for i in r['direct_imports']:
  if i['module'] in objects:assert i['sha256']==objects[i['module']],(module,i)
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
source={}
for attempt in ['rho-resume-inlined-charon-a','rho-resume-inlined-aeneas-c']:
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0;source[attempt]={k:r[k] for k in ['source_revision','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps']};source[attempt]['receipt_sha256']=sha(p.read_bytes())
u=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='WHOLE_ACTUAL_RESUME_WEIGHT_LOOP_CANONICALITY_LENGTH_AND_BYTE_FRAME_CHECKED',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,source_extractions=source,
 producer=dict(base_binary=provenance['base_binary_sha256'],binary=provenance['repaired_binary_sha256'],patch_sha256=provenance['patch_sha256'],source_manifest_sha256=provenance['source_files_manifest_sha256'],changed=provenance['changed']),
 source_binding=['Exact original resume for-loop/assignment and owned locals retained. Exact Reader.k/raw source is expanded at its read call, instantiated at N=16, capture-free and inverse checked. No assumed mutable Reader frame drives extraction.',
 'Whole emitted resume/body/loop Funs is byte-unchanged. Identical field/Reader/Error carriers are aliases; Checkpoint constructor is explicitly transported.',
 'Strict decoder is the already checked actual source. Mutable Vec IntoIterator is the exact std self.iter_mut() wrapper over inherited Vec/slice iterator operations and their original handbacks. No compatible hand-written borrow API or opaque axiom template.'],
 proved=['Successful whole source resume_weights produces only canonical QM31 coefficients, preserves the exact input weight count and Reader.bytes. No input canonicality, decoder-success, fresh-allocation-value, or callback-frame premise.',
 'Proof consumes the complete source loop via a symbolic deferred-handback invariant and actual runtime cursor/updates. It does not normalize 64/256 concrete recurrence terms.'],
 formatter_boundary=dict(kind='inherited opaque Type, not proposition or equivalence law',object_sha256=fmt_object['sha256'],source_sha256=fmt_source['sha256'],note='Same existing unwrap Debug argument as the checked source Reader. Original runtime unwrap ignores this argument; no formatter law assumed.'),
 remaining=['Compose the unchanged complete resume function/header and transaction/query loops.','Finish allocation sufficient-resource/source-allocator connection and final transaction observables.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,print_axioms='N/A receipt audit; exact per-target lists included'))
(ev/'RHO-RESUME-CANONICAL.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
