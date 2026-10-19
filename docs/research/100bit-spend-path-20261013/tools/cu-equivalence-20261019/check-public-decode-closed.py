#!/usr/bin/env python3
"""Candidate-6 completion audit at the unchanged reference source/runtime boundary."""
from pathlib import Path
import hashlib,importlib.util,json,re,resource,subprocess,sys,time
started=time.monotonic();here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
evidence=area/'evidence/cu-equivalence-20261019';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
prior=json.loads(subprocess.check_output([sys.executable,str(here/'check-public-decode-evidence.py')],text=True))
assert prior['status']=='CHECKED_CALLER_AND_PREPARATION_TRANSFER'
kit=here/'public-box-input';pins=read(kit/'source-pins.json')
for name,pin in pins['kit_files'].items():assert sha(kit/name)==pin,name
base=area/'tools/public-binding-followup-kit/first-diagnostic-input';assert sha(base/'lib.rs')==pins['base_kit_lib_sha256']
body=(kit/'boxed-decoder.rs').read_bytes();assert body in (repo/pins['source']['path']).read_bytes()
assert (kit/'lib.rs').read_bytes()==(base/'lib.rs').read_bytes()+b'\nuse alloc::boxed::Box;\n'+body+b'\n'
# No production-source or nominal-carrier change is admitted: interpret the
# emitted wrapper for every S/D/E, then instantiate the existing actual ones.
raw=(here/'public-box-generated/Funs.lean').read_bytes();model=(area/'lean/CuSavingsPublicDecodeClosed.lean').read_bytes()
compact=lambda b:re.sub(rb'\s+',b'',b)
a=raw.index(b'def decode_public_statement_box\n');emitted=raw[a:raw.index(b'\nend AspisR1PublicBox',a)].split(b':= do',1)[1]
a=model.index(b'def boxedSource ');interpreted=model[a:model.index(b'\ntheorem boxed_eq',a)].split(b':= do',1)[1]
replacements=[
 (b'decode_pool_v1_pair_forest_terminal_statement_v1',b'B.decode'),
 (b'core.result.Result.map_err',b'AspisR1PublicPreparation.core.result.Result.map_err'),
 (b'decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorProgramError',b'(decodeErrorClosure invalid)'),
 (b'pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1',b'S'),
 (b'core.ops.control_flow.ControlFlow.Continue',b'.Continue'),
 (b'core.ops.control_flow.ControlFlow.Break',b'.Break'),
 (b'core.result.Result.Ok',b'.Ok'),(b'ProgramError',b'E')]
for before,after in replacements:
 assert before in emitted,before
 emitted=emitted.replace(before,after)
emitted=re.sub(rb'\bval\b',b'statement',emitted)
emitted=re.sub(rb'\bok\b',b'.ok',emitted)
assert compact(emitted)==compact(interpreted),'Complete boxed body differs beyond recorded parametric boundary bindings'
# The only closure ignores its decoder error and returns the one fixed error.
a=raw.index(b'  decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTupleDecodeErrorProgramError.call_once\n');b=raw.index(b'/-- Trait implementation:',a)
closure=compact(raw[a:b].split(b':= do',1)[1]);assert closure==b'okProgramError.InvalidAccountData'
# The original source wrapper itself has one decoder call, one error mapping,
# one Box::new, and no other computation; raw emission confirms Box::new erasure.
assert body.count(b'decode_pool_v1_pair_forest_terminal_statement_v1(bytes)')==1
assert body.count(b'Box::new(')==1 and b'Box' not in raw[raw.index(b'def decode_public_statement_box\n'):raw.index(b'\nend AspisR1PublicBox')]
assert b'import AspisR1PublicBox' not in model and not re.search(rb'^\s*(axiom|sorry|admit)\b',model,re.M)
receipt_dir=evidence/'cu-public-decode-closed-a';r=read(receipt_dir/'receipt.json')
assert r['exit_status']==0 and r['source_sha256']==sha(area/'lean/CuSavingsPublicDecodeClosed.lean')==sha(receipt_dir/'source.lean')
assert r['uncapped_nuc'] and r['resource_authorization']=='User: status update. no nuc limits (2026-10-19)'
assert r['cgroup_limits']=={'memory.high':'max','memory.max':'max','memory.swap.max':'max'}
assert r['process_swaps']>=0 and r['cgroup_swap_bytes']>=0
log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
axioms={name.strip() for block in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log) for name in block.split(',')}
assert axioms<={'propext','Classical.choice','Quot.sound'},axioms
for declaration in ['boxed_eq','projection_eq','adapter_eq','observations_eq','transfer_contract','actual_adapter_eq']:
 assert 'CuSavingsPublicDecodeClosed.'+declaration in log,declaration
assert 'CuSavingsPublicDecodeTransfer.entry_success' in log
assert 'CuSavingsPublicDecodePreparation.entry_helper_parsePublic' in log
# Coherent original decoder/selector/helper closure, not the newer shadow copy.
provenance=r['cache_provenance'];cached=read(receipt_dir/'cache-receipt.json')
assert provenance['sha256']==sha(receipt_dir/'cache-receipt.json')
assert provenance['priority']=='NEW_CU_MODULES_THEN_EXACT_ORIGINAL_CLOSURE'
assert cached['exit_status']==0 and cached['axioms']['passed']
assert sha(repo/r['cache_target_source']['path'])==r['cache_target_source']['sha256']==cached['source_manifest_entry']['source_sha256']
for name,pin in prior['reference_owner_objects'].items():assert provenance['selected_owner_objects'][name]['sha256']==pin,name
order_dir=evidence/'cu-public-decode-order-b';order=read(order_dir/'receipt.json')
assert order['exit_status']==0 and order['source_sha256']==sha(area/'lean/CuSavingsPublicDecodeOrder.lean')==sha(order_dir/'source.lean')
assert order['uncapped_nuc'] and order['cgroup_limits']=={'memory.high':'max','memory.max':'max','memory.swap.max':'max'}
order_log=order['print_axioms_output'];assert 'sorryAx' not in order_log and 'error:' not in order_log
order_axioms={n.strip() for b in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',order_log) for n in b.split(',')}
assert order_axioms<={'propext','Classical.choice','Quot.sound'}
for declaration in ['actual_boxed_eq','select_after_box','argument_order_eq']:
 assert 'CuSavingsPublicDecodeOrder.'+declaration in order_log,declaration
assert order['cache_provenance']['sha256']==sha(order_dir/'cache-receipt.json')
for name,pin in prior['reference_owner_objects'].items():assert order['cache_provenance']['selected_owner_objects'][name]['sha256']==pin,name
callsite_dir=evidence/'cu-public-decode-callsite-a';callsite=read(callsite_dir/'receipt.json')
assert callsite['exit_status']==0 and callsite['source_sha256']==sha(area/'lean/CuSavingsPublicDecodeCallsite.lean')==sha(callsite_dir/'source.lean')
assert callsite['uncapped_nuc'] and callsite['cgroup_limits']=={'memory.high':'max','memory.max':'max','memory.swap.max':'max'}
callsite_log=callsite['print_axioms_output'];assert 'sorryAx' not in callsite_log and 'error:' not in callsite_log
callsite_axioms={n.strip() for b in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',callsite_log) for n in b.split(',')}
assert callsite_axioms<={'propext','Classical.choice','Quot.sound'}
for declaration in ['source_eq','observations_eq']:
 assert 'CuSavingsPublicDecodeCallsite.'+declaration in callsite_log,declaration
all_targets={module:read(evidence/item['attempt']/'receipt.json') for module,item in prior['targets'].items()}
all_targets.update(CuSavingsPublicDecodeClosed=r,CuSavingsPublicDecodeOrder=order,CuSavingsPublicDecodeCallsite=callsite)
for module,rec in all_targets.items():
 for item in rec['direct_imports']:
  if item['module'] in all_targets:assert item['sha256']==all_targets[item['module']]['object_sha256'],(module,item['module'])
for directory,rec in [(receipt_dir,r),(order_dir,order),(callsite_dir,callsite)]:
 cache=read(directory/'cache-receipt.json');prov=rec['cache_provenance']
 assert prov['sha256']==sha(directory/'cache-receipt.json')
 for name,item in prov['selected_cache_objects'].items():
  expected=cache['objects']['.olean'] if name==cache['target'] else cache['key']['imports'][name]['objects']['.olean']
  assert item['sha256']==expected['sha256'],name
emission={}
for attempt in ['cu-public-box-charon-a','cu-public-box-aeneas-a']:
 q=read(evidence/attempt/'receipt.json');assert q['exit_status']==0 and q['source_pins_sha256']==sha(kit/'source-pins.json')
 assert q['uncapped_nuc'] and q['limits']=={'memory.high':'max','memory.max':'max','memory.swap.max':'max'}
 if 'aeneas' in attempt:
  assert q['frontend_binary_sha256']=='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
  assert '-checks' in q['command'] and '-abort-on-error' in q['command']
 emission[attempt]=dict(receipt_sha256=sha(evidence/attempt/'receipt.json'),exit_status=q['exit_status'])
requirements={
 'exact_source_delta':dict(status='PROVED_AT_REFERENCE_BOUNDARY',evidence='Existing whole first/stage1 source checks; exact newly emitted boxed wrapper; recorded complete-body parametric substitutions.'),
 'same_immutable_bytes_and_projection':dict(status='PROVED',evidence='Source binding pin; boxed_eq and axiom-free projection_eq using original Aeneas Box.deref.'),
 'call_argument_evaluation_order':dict(status='PROVED',evidence='Actual decoded-value selector is total; argument_order_eq commutes it past arbitrary argument construction with no exported decode-success premise.'),
 'all_result_paths_and_context_observations':dict(status='PROVED',evidence='CuSavingsPublicDecodeCallsite.source_eq and observations_eq consume boxed decode and total actual selection together, with arbitrary argument construction and common context. No success/equivalence premise.'),
 'existing_reference_results_consumed':dict(status='PROVED',evidence='Actual decoder/selector bindings, entry_success, entry_helper_parsePublic; transfer_contract consumes any existing reference contract.'),
 'focused_checks_and_pins':dict(status='VERIFIED',evidence='Current source/receipt hashes, coherent original owner cache, strict source emission, exact #print axioms outputs and resource receipts.'),
 'scope':dict(status='UNCHANGED',evidence='Original faithful source translation, Box/SDK/runtime and sufficient-resource boundary retained. No proof of SDK/compiler correctness added or claimed; other nine changes and combined security transfer remain open.')}
u=resource.getrusage(resource.RUSAGE_SELF)
result=dict(status='CANDIDATE_6_EQUIVALENCE_COMPLETE_AT_EXISTING_REFERENCE_BOUNDARY',candidate=pins['candidate'],reference_parent=pins['candidate']+'^',production_revision=pins['production_revision'],requirements=requirements,
 theorem_source_sha256=r['source_sha256'],theorem_receipt_sha256=sha(receipt_dir/'receipt.json'),raw_emission_sha256=sha(here/'public-box-generated/Funs.lean'),emission=emission,
 argument_order_source_sha256=order['source_sha256'],argument_order_receipt_sha256=sha(order_dir/'receipt.json'),
 callsite_source_sha256=callsite['source_sha256'],callsite_receipt_sha256=sha(callsite_dir/'receipt.json'),
 parametric_body_substitutions=[(a.decode(),b.decode()) for a,b in replacements],
 inherited_boundaries=['Faithful source-model interpretation used by the reference, including immutable account borrows.','Original Aeneas Box interpretation and unchanged enclosing SDK/runtime context.','Logical executions with sufficient resources; timing/CU/heap-exhaustion behavior is outside the original observation relation.'],
 added_equivalence_premises=[],other_optimizations_complete=False,combined_security_transfer_complete=False,
 command=[sys.executable,str(Path(__file__).relative_to(repo))],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),features=['r0','private-leaf-salts'],exit_status=0,
 wall_seconds=time.monotonic()-started,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,
 print_axioms='N/A: completion/source audit; focused theorem and original consumed results audited above')
print(json.dumps(result,indent=2))
