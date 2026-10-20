#!/usr/bin/env python3
"""Requirement audit of the exact candidate-12 production caller proof closure."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['check-rho-optimized-traversal.py','check-rho-accumulate.py','check-rho-resume.py','check-rho-initialization-canonical.py','check-rho-query-stage.py']:
 subprocess.run([sys.executable,str(tool/name)],check=True,capture_output=True)
for name in ['extract-rho-resume-caller.py','extract-rho-transactions.py','emit-rho-resume-caller.py','emit-rho-transactions.py']:
 subprocess.run([sys.executable,str(tool/name),'--check'],check=True,capture_output=True)
targets={
 'AspisR1RhoBump/Types':'rho-bump-types-b',
 'AspisR1RhoBump/FunsExternal':'rho-bump-externals-a',
 'AspisR1RhoBump/Funs':'rho-bump-funs-a',
 'CuSavingsRhoBump':'rho-bump-proof-f',
 'CuSavingsRhoAllocationSuccess':'rho-allocation-success-c',
 'CuSavingsRhoResourceAdmission':'rho-resource-admission-a',
 'CuSavingsRhoEntryTransport':'rho-entry-transport-b',
 'AspisR1RhoResumeCaller/Types':'rho-resume-caller-types-b',
 'AspisR1RhoResumeCaller/FunsExternal':'rho-resume-caller-externals-b',
 'AspisR1RhoResumeCaller/Funs':'rho-resume-caller-funs-a',
 'CuSavingsRhoResumeCaller':'rho-resume-caller-proof-f',
 'AspisR1RhoTransactions/Types':'rho-transactions-types-a',
 'AspisR1RhoTransactions/FunsExternal':'rho-transactions-externals-b',
 'AspisR1RhoTransactions/Funs':'rho-transactions-funs-a',
 'CuSavingsRhoTransactions':'rho-transactions-proof-d',
 'CuSavingsRhoCallerClosure':'rho-caller-closure-a',
 'CuSavingsRhoCryptographicTrace':'rho-cryptographic-trace-a',
 'CuSavingsRhoCandidate12':'rho-candidate12-final-b'}
# Import objects in the earlier milestones must agree with the final consumers.
prior=json.loads((ev/'RHO-QUERY-STAGE.json').read_text())['successes']
objects={m.replace('/','.'):r['object_sha256'] for m,r in prior.items()}
receipts={};results={}
for module,attempt in targets.items():
 rp=ev/attempt/'receipt.json';r=json.loads(rp.read_text());assert r['exit_status']==0,(module,r['exit_status'])
 src=(area/'lean'/(module+'.lean')).read_bytes();assert sha(src)==r['source_sha256'];assert src==(ev/attempt/'source.lean').read_bytes()
 assert not re.search(rb'(?m)^\s*(?:axiom|constant)\s|\b(?:sorry|admit)\b',src),module
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 declarations=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert declarations
 allowed={'propext','Classical.choice','Quot.sound'}
 if 'ResumeCaller' in module or module in ['AspisR1RhoTransactions/FunsExternal','AspisR1RhoTransactions/Funs','CuSavingsRhoTransactions','CuSavingsRhoCandidate12']:allowed|={'core.fmt.Formatter','Aeneas.Std.core.fmt.Formatter'}
 for name,axs in declarations:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<=allowed,(name,axs)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 receipts[module]=r;objects[module.replace('/','.')]=r['object_sha256']
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']};results[module].update(attempt=attempt,receipt_sha256=sha(rp.read_bytes()))
for module,r in receipts.items():
 for entry in r['direct_imports']:
  if entry['module'] in objects:assert entry['sha256']==objects[entry['module']],(module,entry)
# Raw source function bodies: only namespace instance parameters are added.
for raw,module,params in [
 ('rho-resume-caller-generated','AspisR1RhoResumeCaller','variable [ResumeCommon]\n'),
 ('rho-transactions-generated','AspisR1RhoTransactions','variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon] [AspisR1CuRho.HeapReserve] [AspisR1RhoResumeCaller.ResumeCommon] [TxCommon]\n')]:
 actual=(area/'lean'/module/'Funs.lean').read_text();assert actual.replace(params,'',1)==(tool/raw/'Funs.lean').read_text()
for n in ['Types.lean','Funs.lean']:assert (tool/'rho-bump-source-generated'/n).read_bytes()==(area/'lean/AspisR1RhoBump'/n).read_bytes()
# Exact pinned Solana allocator arithmetic and its pointer-load/store erasure.
bump=json.loads((tool/'rho-bump-source-input/source-pins.json').read_text());body=(tool/'rho-bump-source-input/original-alloc.rs').read_bytes();assert sha(body)==bump['alloc_source_sha256']
for literal in [b'let mut pos = *pos_ptr;',b'pos = self.start + self.len;',b'pos = pos.saturating_sub(layout.size());',b'pos &= !(layout.align().wrapping_sub(1));',b'if pos < self.start + size_of::<*mut u8>()',b'*pos_ptr = pos;']:
 assert literal in body,literal
assert sha((tool/'rho-bump-source-input/lib.rs').read_bytes())==bump['lib_sha256']
lock=(repo/'Cargo.lock').read_text();assert 'name = "solana-program-entrypoint"\nversion = "2.3.0"' in lock
assert bump['crate_checksum']=='32ce041b1a0ed275290a5008ee1a4a6c48f5054c8a3d78d313c08958a06aedbd'
origin=json.loads((tool/'rho-raw4-reservation-source/origin.json').read_text())
for entry in origin['files'].values():assert sha((tool/'rho-raw4-reservation-source'/entry['file']).read_bytes())==entry['slice_sha256']
raw=(tool/'rho-raw4-reservation-source/raw_vec-mod.rs').read_text();layout=(tool/'rho-raw4-reservation-source/core-src-alloc-layout.rs').read_text();global_alloc=(tool/'rho-raw4-reservation-source/alloc.rs').read_text()
for literal in ['Self { ptr, cap: ZERO_CAP, alloc }','additional > self.capacity(elem_layout.size()).wrapping_sub(len)','len.checked_add(additional).ok_or(CapacityOverflow)?','self.alloc.allocate(new_layout)','self.set_ptr_and_cap(ptr, cap)','elem_layout.size() == 0 || self.cap.as_inner() == 0','elem_layout.repeat_packed(cap)']:
 assert literal in raw,literal
for literal in ['self.size.checked_mul(n)','Layout::from_size_alignment(size, self.align)','size <= Self::max_size_for_alignment(alignment)','unchecked_sub(isize::MAX as usize + 1, alignment.as_usize())']:
 assert literal in layout,literal
assert 'NonNull::new(raw_ptr).ok_or(AllocError)?' in global_alloc
# Trace projection has identical prefix source, no accumulator/pending input.
qp=json.loads((tool/'rho-query-context-input/source-pins.json').read_text());assert qp['no_accumulator_or_pending_input_to_common_prefix']
prefix=(tool/'rho-query-context-input/fragments/common-prefix.rs').read_bytes();assert sha(prefix)==qp['common_prefix_sha256'];assert b'hash' in prefix
# No cryptographic operation in any changed arithmetic/memory kernel.
for f in [tool/'rho-accumulate-input/fragments/new-accumulate.rs',tool/'rho-query-context-input/fragments/new-node.rs',tool/'rho-bump-source-input/lib.rs']:
 assert not re.search(rb'\b(?:digest|merkle_path|leaf_with_digest|private_leaf_hash_with_digest)\s*\(',f.read_bytes()),f
# Exact source/no protocol edits; all earlier production gates remain applicable.
frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
assert subprocess.check_output(['git','-C',str(repo),'diff',frozen,'--','crates','programs'])==b''
inv=json.loads((ev/'RHO-CANDIDATE12-DECLARATION-REPIN.json').read_text());assert len(inv['declarations'])==11
assert set(inv['counts'])=={'new-source-bound','unchanged-forwarder-with-none-argument','re-extracted-source-context'}
# These are the actual production source roots named by the objective.
root_source=(area/'lean/CuSavingsRhoTransactions.lean').read_text()
for n in ['tx1_finish_equivalence','tx2_equivalence','tx2_authenticated_equivalence']:assert 'theorem '+n in root_source
bridge=(area/'lean/CuSavingsRhoCandidate12.lean').read_text();assert 'theorem all_callers_equivalence' in bridge
runtime_path=area/'evidence/cu-savings-20261019/FINAL-REPORT.md';assert '**1,199,687**' in runtime_path.read_text() and '**1,188,496**' in runtime_path.read_text()
u=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='CHECKED_SOURCE_CALLER_CLOSURE_WITH_EXPLICIT_RESOURCE_AND_RUNTIME_BOUNDARY',candidate=inv['candidate'],parent=inv['parent'],production_revision=frozen,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),candidate_complete=True,publication_pending=True,
 requirements={
 '1_initialization_and_allocation':'Actual new/zip and heap helper consumed. Empty std wrapper frame; exact source BumpAllocator arithmetic; source raw4 layout/capacity guards pinned and discharged numerically for n<=256. Full initializer success follows from start+8+8199+future<=cursor under the explicit 64-bit target ABI. No allocation-success/equivalence premise is supplied.',
 '2_accumulation_and_callers':'Whole actual coefficient/basis/accumulation/query/stage contexts consumed. Canonical rho/power/weights and length derive from actual preparation/constructor/resume sources; index/counter/coverage/overflow invariants established by source traversal and whole-call preservation.',
 '3_source_transactions_and_observations':'All three named actual transaction source bodies are inverse-factored at the proved stage; emitted bodies otherwise byte unchanged. Final source-consuming all_callers_equivalence plus fresh_source_equivalence, tx2_equivalence and tx2_authenticated_equivalence check. Query prefix invocation trace and arbitrary expanded ordered event trace check; exact source prefix has identical inputs and contains all query cryptographic calls. Same complete materialized state enters unchanged checkpoint and finish/settlement suffixes. Covered errors/divergence retained under sufficient logical resources.',
 '4_pins_and_lean':'Exact candidate/parent and frozen current source, producer repair pins, source fragments, coherent cache/import object identities, focused checks and final consuming bridge with complete axioms/metrics below.',
 '5_publication':'Side-branch commit/push remains a separate final publication check; no production Rust edited. No ELF/shared object/cache binary is part of this source proof.'},
 boundary=['Relative to the existing Rust/Aeneas primitive interpretation, compiler/producer and standard-library pointer ownership/Vec capacity/resize contracts. This is a source replacement proof, not a new machine-code/compiler or whole-Rust-stdlib correctness theorem.',
 'The Raw4 empty-buffer reserve interpretation is justified by the pinned actual std call chain: cap=len=0; zero count no-op; checked add/mul and Layout guards admitted; current_memory=None; one Global.allocate call through the source bump allocator; cap assigned to count; resize within reserved capacity. No nonempty reserve/copy behavior is required.',
 'The numeric condition is at the extra reservation boundary. future is a budget for unchanged remaining allocations and is preserved by the source bump bound. It is not an assertion that all 256 KiB are free or a universal fixture/input CU bound.',
 'Inherited opaque core.fmt.Formatter is a Type used by the original Reader unwrap Debug argument; it is not a new propositional or candidate-equivalence axiom. No sorryAx appears in accepted targets.',
 'Production features pool-adapter,private-leaf-salts, no prover. Prover-only intermediate trace canonicalization and arbitrary standalone convenience-helper consumers are outside these three selected release entrypoints. Both public None forwarding wrappers are inventoried without attributing a general helper theorem to them.',
 'Actual trace::value calls are no-ops in the selected non-prover feature set. Transient raw coefficient representation is projected through the actual source finish; diagnostic logs are excluded from the protocol observation boundary. Phase callbacks and application effects follow the identical source contexts.'],
 successes=results,earlier_checked_milestone_sha256={n:sha((ev/n).read_bytes()) for n in ['RHO-OPTIMIZED-TRAVERSAL.json','RHO-ACCUMULATE.json','RHO-RESUME-CANONICAL.json','RHO-INITIALIZATION-CANONICAL.json','RHO-QUERY-STAGE.json']},
 runtime_reuse=dict(path=str(runtime_path.relative_to(repo)),sha256=sha(runtime_path.read_bytes()),note='Frozen production Rust unchanged; no unchanged SBF/CU/injection replay. The six measured fixtures remain below1.2M; this goal adds the candidate12 source proof, not other optimization proofs.'),
 remaining_other_work=['Other retained optimization proofs and the combined soundness/privacy transfer remain separate. No whole-bundle formal-completion claim.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,print_axioms='N/A source/receipt audit; exact per-target Lean results included'))
(ev/'RHO-CANDIDATE12-FINAL.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
