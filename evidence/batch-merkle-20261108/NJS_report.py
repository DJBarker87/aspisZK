"""Assemble final handoff from retained, validated evidence; no ledger mutation."""
from pathlib import Path
import hashlib,json,lzma,subprocess,collections
E=Path(__file__).resolve().parent
J=lambda name:json.loads((E/name).read_text())
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
closed=J('NJS_CLOSED.json');packets=J('NJS_ROW_PACKETS.json');ids=sorted(r for f in closed['functions'] for r in f['rows'])
bpath=E.parent/'ledger15-20261108/NJO_LEDGER.json.xz';raw=lzma.decompress(bpath.read_bytes());baseline=json.loads(raw)
assert baseline['counts']['CLOSED']==463,baseline['counts']
rows=json.loads(lzma.decompress((E/'NJS_BASELINE_ROWS.json.xz').read_bytes()));remaining=[r for r in rows if r['row'] not in ids]
assert len(remaining)==7
why={
 'batch_tree':'Its real verify_in_place child is OPEN: TX1:127 / TX2:093. The merged NJP handoff explicitly lacks transaction-specific entry/wrapper, caller-domain and adopted-endpoint packets. Shared row/height/abort support cannot replace that CLOSED child. This out-of-slice dependency cannot be authored in NJS; bottom-up ruling forbids a parent certificate with a free verifier or successful-child premise.',
 'batch_merkle_values':'Its actual batch_tree child (TX1:083 / TX2:055) remains OPEN for the verifier dependency. Composing the wrapper now would retain an unresolved child Result/endpoint, forbidden by (aq). No independent child remains within this member.',
 'batch_merkle':'Its actual batch_merkle_values child (TX1:082 / TX2:054) remains OPEN, transitively through batch_tree and verify_in_place. The sole-child wrapper cannot reach a CLOSED root before that dependency; an arbitrary operation dictionary is not a replacement.',
 'canonical_scan':'Its real echeck child (TX1:189) is OPEN and outside the explicit NJS function list. NJC/NJJ partial cuts are retained read-only support, not a history-provider endpoint proof. Completing echeck would violate the slice boundary; a successful-history or arbitrary-echeck premise is forbidden.'}
future={
 'batch_tree':'After verifier admission: native arbitrary-prestate loop/branch/abort cuts with controls and Lean loop induction plus exact caller-domain composition. Shared NJP support may then be consumed from its merged source. This is not blocked by exhausted Kani; the currently missing sibling entry/caller obligations are Lean-only and out of scope.',
 'batch_merkle_values':'After batch_tree closes: bind the existing emitted body to its SAME child Result and complete native/source wrapper observation. No further native attempt is justified before the real child closes.',
 'batch_merkle':'After batch_merkle_values closes: compose SAME input, full Result and rejection prefixes. Native cut/control only if not already entailed by admitted wrapper transport; no missing Kani result is asserted now.',
 'canonical_scan':'First obtain a CLOSED echeck/history-provider child outside this slice. Then compose existing NJC/NJJ prefix/field cuts, full Result/history trace, and remaining native step/control and Lean induction if required. No claim that Kani exhaustion blocks a Lean-only proof.'}
text='''# Remaining obligations and early-stop justification

Target not yet established.19 row candidates are locally validated; authoritative ledger credit waits for the next lead gate. The baseline remains463 CLOSED /0 provisional /136 OPEN. No authoritative row was edited.

Budget used:39/100 Kani;64/100 Lean/link/audit scopes plus6 noncompiler preflight/support scopes (70/100 charged conservatively);1/1 extraction. No timeout or memory kill occurred. All heavy work had MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; no cap or timeout was raised. This is an explicit below80-percent stop justification, not budget exhaustion.

The binding bottom-up/slice-boundary rules leave no unattempted independent member. All19 independent occurrences have complete candidate packets and the final gate. Repeating their unchanged proofs would not resolve a remaining obligation. Every remaining occurrence is listed separately below. No new in-scope Lean-only obligation can close one of these roots without its actual external child; the missing verifier entry/caller obligations are explicitly Lean-only in the sibling report, and are outside NJS scope.

| Remaining row | Member | Why no further admissible attempt can close it now |
| --- | --- | --- |
'''
for r in sorted(remaining,key=lambda r:r['row']):
 name=r['function'].split('::')[-1];text+=f"| {r['row']} | {name} | {why[name]} |\n"
text+='\nFuture native/Lean requirements, without attributing a Lean-only blocker to Kani exhaustion:\n\n'
for r in sorted(remaining,key=lambda r:r['row']):text+=f"- {r['row']} {r['function'].split('::')[-1]}: {future[r['function'].split('::')[-1]]}\n"
text+='\nAll26 members accounted for:\n\n| Row | Member | Final worker disposition |\n| --- | --- | --- |\n'
for r in sorted(rows,key=lambda r:r['row']):
 name=r['function'].split('::')[-1];state='Complete local candidate; no unproved local theorem remains; next lead ledger admission only.' if r['row'] in ids else 'OPEN; exact blocker above.';text+=f"| {r['row']} | {name} | {state} |\n"
text+='\nLatest sibling check: NJP merged at research 47477b58165; research ref at inspection a8863b281c90. Its merged final handoff retains BOTH verify_in_place rows OPEN. NJS_MERGED_NJP_INPUTS.json pins the read-only content; no sibling worktree was accessed. No other lane or pending runtime trust row is used.\n'
(E/'NJS_REMAINING.md').write_text(text)
validation=J('NJS_VALIDATION.json');closed['status']='LOCALLY VALIDATED candidate packets; authoritative CLOSED credit pending next lead ledger gate';closed['validation']='NJS_VALIDATION.json';closed['admission']='NJS_AUDIT.json';closed['security_target_established']=False
for f in closed['functions']:f['local_status']='LOCALLY VALIDATED CANDIDATE; next authoritative ledger gate pending'
(E/'NJS_CLOSED.json').write_text(json.dumps(closed,indent=2)+'\n')
for p in packets:p['status']='LOCALLY VALIDATED CANDIDATE; ledger pending'
(E/'NJS_ROW_PACKETS.json').write_text(json.dumps(packets,indent=2)+'\n')
delta={'operation':'additive candidate packet validation only; no authoritative ledger mutation','basis':'evidence/ledger15-20261108/NJO_LEDGER.json.xz','basis_compressed_sha256':hashlib.sha256(bpath.read_bytes()).hexdigest(),'basis_uncompressed_sha256':hashlib.sha256(raw).hexdigest(),'baseline_counts':baseline['counts'],'candidate_closed_rows':ids,'added_closed_rows':ids,'still_open_rows':sorted(r['row'] for r in remaining),'locally_validated_count':19,'lead_gate_credit':'PENDING','projected_counts_if_only_these19_are_admitted':{'CLOSED':482,'PROVISIONAL':0,'OPEN':117,'total':599},'authoritative_ledger_changed':False,'security_target_established':False,'trust_change':'none; retained P6/D188 option A reclassification, runtime SHA=H and pinned Std/ABI/compiler/source-to-ELF trust','validation':'NJS_VALIDATION.json','validation_sha256':hashlib.sha256((E/'NJS_VALIDATION.json').read_bytes()).hexdigest(),'audit':'NJS_AUDIT.json','source_revision':rev}
(E/'NJS_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
export=J('NJS_EXPORT.json');seed=J('NJS_SEED.json');attempts=[json.loads(l) for l in (E/'NJS_ATTEMPTS.jsonl').read_text().splitlines()]
maxrss=max(int(r['peak_rss_kib']) for r in attempts);wall=sum(r['wall_seconds'] for r in attempts)
handoff=f'''# NJS batch Merkle handoff

Target not yet established.19 of26 requested row occurrences have locally validated candidate packets; seven remain OPEN. No authoritative ledger promotion or soundness claim. Baseline ledger15 remains463 CLOSED /0 provisional /136 OPEN. Next lead gate decides credit.

Completed functions: batch_key_at, same_batch_index, same_batch_leaf, parent_with_digest, private_leaf_hash_with_digest, slot, batch_leaf, parse_shape, batch_keys, sort_batch_keys. Both paths are separately checked by original obligation/body/clause hashes; shared native certificates apply only to identical frozen monomorphizations. Exact19 row IDs, roots, domains and14 positive/control pairs are in NJS_CLOSED.json; operation-specific original caller clauses in NJS_ROW_PACKETS.json. Root statements/hypotheses in NJS_ROOT_STATEMENTS.md and L055/stdout.log.

Remaining: TX1:083/TX2:055 batch_tree need OPEN verify_in_place TX1:127/TX2:093; TX1:082/TX2:054 batch_merkle_values and TX1:081/TX2:053 batch_merkle follow that real dependency. TX1:084 canonical_scan needs OPEN out-of-slice echeck TX1:189. The merged NJP result does not close either verifier row. Read-only pins NJS_MERGED_NJP_INPUTS.json; exact per-member below80-percent stop reasons and future requirements in NJS_REMAINING.md. No arbitrary Ops/child-success/endpoint premise is used to hide these blockers.

Validation: NJS_VALIDATION.json PASS. One combined raw ax2 walk:40/40 roots, includes AspisR1.RPx_Deployed.deployed, complete traversal equals collector, only propext/Classical.choice/Quot.sound. Same binary detects four planted axioms and clears four mutations. Final strict NFX-style scan:15,713 modules, zero dangling references/duplicate owners/import mismatches. First scan found only9 missing expected-import entries; independently pinned source imports repaired it; second/final scan passes. No further full audit was run. NJS_AUDIT.json and exact capped-scope receipts retain target, status, wall/RSS/swap/source revision/axioms. Across all completed scopes wall sum={wall:.3f}s, maximum recorded RSS={maxrss}KiB; zero swap; no timeout/memory kill. These are measured scope totals, not a new machine-performance claim.

Budget:39/100 Kani,64 Lean/link/audit plus6 preflight/support (70/100 conservatively),1/1 extraction. The sole extraction emitted all12 candidate.rs targets. The two foreign core bodies remained opaque; native exact byte/reply cuts plus the existing pinned NDH safe-reference extraction/runtime grammar law are used explicitly, not represented as newly emitted core bodies. Raw extraction, additive selector diff, library models, cuts/stubs and source adaptation diffs are retained. Loops use one native arbitrary-prestate iteration plus Lean induction; full arrays/frame and all Results are retained. Digest values remain the approved runtime SHA=H trust. Every credited copy-dependent native pair uses the exact KMX patch and an identical-source semantic failing control. K034/035,036/037,038/039 replace three older pairs with interleaved snapshot changes. No field multiplication, function-contract, Option<fn>, writable-static, or suspended prior-native credit.

Host retained workspace: /home/dombarker/project-offloads/codex-cx-batch-merkle-20261108. Own CARGO_TARGET_DIR in every receipt: .../NJS_target (rebuildable output removed after completion). Own source/objects/seed/cache retained. Seeded by COPYING NJO export first then NJE: {seed['bytes']} bytes; every imported hash in NJS_SEED.json. Export: {export['export']}, {export['bytes']} bytes/{len(export['files'])} files, hashes NJS_EXPORT.json. Resolve LEAN_PATH exactly from NJS_PATHS.json; every Lean/audit receipt pins resolved Aeneas objects and selected imports. No shared cache or sibling/session-A worktree was modified; no wallet/key action. Final strict frozen graph/lock validation passes offline. Only own Cargo output was deleted, per NJS_CLEANUP.json; no retained cache deleted.

Shipped crates/programs/Cargo.lock are byte-identical to frozen 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; harness changes exist only in scratch and committed patches/inputs. No ELF rebuild trigger. Inherited hashes remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. They were not newly rebuilt here. No trust row added/removed; RuntimeCpiReadonlyEntry7 unused. Digest/error slots43/44 preserved.

Review/reproduce local consistency: python3 evidence/batch-merkle-20261108/NJS_validate.py. Repeated immutable inputs are losslessly pooled once by SHA256 in NJS_inputs; NJS_POOLED_INPUTS.json and NJS_resolve.py reconstruct each original path and verify its hash. All inputs are committed; none is hidden by ignore rules. No file exceeds20MB. Scope failures and their exact replacements remain in NJS_FAILING_STEP.md; no failure is erased or relabeled a pass. Native/Lean/source/ledger/security claims remain distinct.

Audit-stage commit: {rev}. Final report and handoff are committed separately. Do not push. Continuation must use the retained workspace/objects and remaining budget, one admitted capped scope at a time; no new extraction remains. Resume parent work only after the actual verifier/echeck child bridges are CLOSED and their full caller domains can be instantiated. Do not replay unchanged raw audit or full regressions.
'''
(E/'NJS_HANDOFF.md').write_text(handoff)
print('final handoff/ledger delta generated;19 candidates;7 individually justified dependency blockers')
