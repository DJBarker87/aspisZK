#!/usr/bin/env python3
"""Build review tables from the committed row map and Rc7 premise inventory."""
import collections,json,pathlib
D=pathlib.Path(__file__).resolve().parent;R=D.parent.parent
m=json.loads((D/'NFL_ROW_TO_CONE.json').read_text()); rows=m['rows']
rc=json.loads((R/'evidence/recount7-20261026/Rc7_premises.json').read_text())
cones={
'S1':('preparation/transcript driver, Prepared/claim/scratch binding','Retired N001–N046, N108–N115; L122–L124/L126/L129–L132/L139–L141/L168','CLOSED for historical accepted preparation families','SAME accepted preparation laws remain historically retired; the three native subject roots in this later occurrence ledger are OPEN. No contradiction: the domains and status units differ. Full caller/refinement and shared deployment gates remain.','SAP_PrepareOwner.installed; SAP_Binding.prepare; F3Y_InstalledLaws.prepare; SAP_SaveOnRun.saved; TxS_Encoding.model; SAF_AcceptedValue.value'),
'S2':('dispatcher/adapter/header, same native caller and physical history','L159 (alias L185), L166, L181; retired dispatcher/header N117/N118 and L088–L099/L155–L158/L160–L165/L180/L182–L184','OPEN; adopted portions TRUST','Source-local entry/adapter composition is OPEN. Close StoredCarrierBinding, exact accepted Result/effects plus rejected-prefix reads and whole oracle experiment/history association. Slice result bytes do not associate Pool return data.','Rc7_Native.accepted; Rc7_Top.deployed; Rc10_Top.deployed (conditional consumers, not retained-row discharges)'),
'S3':('row/group/Weights::pair','L133–L138/L142/L144–L146 and corresponding F3Y_G_ families; retired N047–N074','OPEN','Native/global L142/L144–L146 remain after historical round retirements. Weights::pair and semantic subject cuts are OPEN outside both slices. Need exact dual-fold pair and semantic initial/chain/masked terminal laws on their full, distinct domains.','F3Y_InstalledLaws.primitives; FIs_OnRun.strengthen/FIs_Finish.strengthen (historical rounds only)'),
'S4':('four dots','L143 and F3Y_G_L143; retired N047–N088/L148 support','OPEN','Both four_dots roots remain OPEN in Q. CLOSED decode/reducer/new/finish helpers do not cover Dot::push and the SAME-view all22 matching equations; native/global L143 remain.','Installed primitive support; historical FIp concrete query installation, without matching-family discharge'),
'S5':('strict decode/tower/pairing/dot kernels','L133–L138/L142/L147 and corresponding F3Y_G_ families; retired N052–N069/N075–N079/L110–L121/L125/L127/L128/L148','OPEN','L142 native/global Pair remains. Historical FIs round/final-dot retirements are reused; Q arithmetic helpers do not complete Pair, reached operands, source-machine/state and caller interpretation.','FGm_Aligned.values; FGm_Join.accepted_raw_join_or_collision; FIs_OnRun.strengthen; FIs_Finish.strengthen'),
'S6':('decoder/public/TX1/checkpoint, including forest/Claims','L176 historically retired at Rc8; retired L091–L093/L099/L149/L150/L165/L171–L175/L177/L179/N115','CLOSED for historical listed accepted families under retained trust','Preserve scoped S6N retirement. Slice S adds conditional source-path coverage, not a new retirement; TX1 driver, checkpoint and resume occurrence subjects remain OPEN. Full deployed closure still needs same runtime bytes/history, ownership/errors/adoption and trust-instance association.','S6N_Installation.facts/accepted; S6N_Decoder.complete; S6N_Getters.complete'),
'S7':('query values/geometry/inverses/batched accumulation and matching','L143/F3Y_G_L143; shared L159/L166/L181; retired N047–N107/L149/L150/L169/L170','OPEN','Q has 0/2 CLOSED roots: query_loop OPEN and QueryGeometry::for_range QUALIFIED in both TXs. Need coherent retarget replay for geometry qualification, caller composition of remaining query functions, native/global matching and shared deployment association.','F3Y_InstalledLaws.primitives/canonical/domain/multiply/one/inverse; Rc4_Assemble.deployed (historical primitive support)'),
'S8':('accumulator/residue/compact finish; shared parser/multiproof joins','L147/F3Y_G_L147 historically retired by Rc10; shared L159/L166/L181; retired L100–L109/L149/L150/L170/L173/L195–L199','OPEN at deployment boundary','Two residue-update occurrences are CLOSED in Q, while Accumulator::new, compact checking/expansion and finish_query_dot remain OPEN outside slices. Historical dot-family retirement does not close this later native occurrence coverage. Shared full batch/runtime/oracle gates remain.','P6C_Extension.boundary/source_preserved; P6C_FullBoundary.same_cuts; FIs_OnRun.strengthen/FIs_Finish.strengthen'),
'S9':('factored Libra weights','L142/L144–L146 plus round L133–L138 and corresponding F3Y_G_ families; retired N070–N074','OPEN','Factored root TX2:133 is OPEN outside Q/S. CLOSED generic field operations do not instantiate FunctionalWeights, dual-fold pair or masked terminal equations; L142/L144–L146 native/global remain.','Installed semiring/primitive support and accepted finish transport only; no new exact FunctionalWeights instance'),
'S10':('all source sites and continuations, including errors; artifact correspondence','L166/L181 and historically L176; L187/L188; L186 accepted retirement; P7/P6 TRUST','OPEN; lowering subrow historically CLOSED','366 OPEN and 2 QUALIFIED sites remain. Need complete source/error/ownership/oracle continuation coverage and coherent final dependency replay L187 plus final axioms/trust/adoption/artifact association audit L188. No new artifact correspondence/rebuild here.','Low2_source_to_elf_manifest.json/Low2_final_receipt.json (accepted L186 retirement under P7); Rc10 conditional source joins')}
# Exact candidate cuts, never an asserted theorem-domain equivalence.
C='crates/aspis-r1-cost-probe/src/'
def fs(file,*names):return [C+file+'::'+n for n in names]
Pmap={}
for n in range(133,139):Pmap[f'L{n}']=(['S3','S5','S9'],fs('verifier.rs','finish_relation_round'))
Pmap.update({'L142':(['S3','S5','S9'],fs('weights.rs','Weights::pair')),'L143':(['S4','S7'],fs('candidate.rs','query_loop')+fs('fast_dots.rs','four_dots')),'L144':(['S3','S9'],fs('r1_semantic.rs','semantic_boundary','semantic_rounds','verify_finish')),'L145':(['S3','S9'],fs('r1_semantic.rs','semantic_rounds','verify_finish')),'L146':(['S3','S9'],fs('r1_semantic.rs','verify_finish')),'L147':(['S5','S8'],fs('verifier.rs','finish_query_dot')),'L154':([],[]),'L159':(['S2','S7','S8'],[]),'L166':(['S2','S7','S8','S10'],fs('candidate.rs','batch_merkle')+fs('multiproof.rs','verify_in_place')),'L176':(['S6','S10'],[f for f in m['anchors']['S6']['functions'] if '::tx1' not in f and '::checkpoint' not in f and '::resume' not in f]),'L181':(['S2','S7','S8','S10'],[]),'L185':(['S2','S7','S8'],[]),'L187':(['S10'],[]),'L188':(['S10'],[])})
prem=[]
for p in rc['rows']:
 if p['classification']!='P':continue
 base=p['id'].replace('F3Y_G_',''); cs,ff=Pmap[base]
 historical=base in [f'L{n}' for n in range(133,139)]+['L147','L176']
 receipt='evidence/recount10-20261026/Rc10_059/receipt.json' if historical else None
 cand=[r for r in rows if r['function'] in ff]
 prem.append({'id':p['id'],'meaning':p['meaning'],'cones':cs,'candidate_rows':[r['row'] for r in cand], 'candidate_counts':dict(collections.Counter(r['composed_status'] for r in cand)),'disposition':'historical accepted retirement in dated Rc8/Rc10 append; zero new credit' if historical else ('alias of L159; zero independent credit' if base=='L185' else 'UNTOUCHED retained premise; no accepted discharge established by this mapping'),'historical_receipt':receipt,'new_discharge':False,'gap':'No function occurrence represents this quantified budget/runtime/experiment/release obligation.' if not ff else 'Candidate implementation sites are not an equivalence proof for the complete Rc7 quantified premise; CLOSED helper rows alone are insufficient.'})
(D/'NFL_PREMISE_COVERAGE.json').write_text(json.dumps(prem,indent=2)+'\n')
header='''# NFL cone map refresh — 4 November 2026

**Numbers are status, not new credit. Target not yet established.**

This is a mapping over existing receipts; no Lean, Kani, Rust, extraction, native build, cold replay or fresh axioms audit ran. NFK has **219 CLOSED / 2 QUALIFIED / 366 OPEN of 587 occurrences**, not 219 discharged theorem premises. Q: **126/149 CLOSED, 2 QUALIFIED, 21 OPEN; 0/2 roots CLOSED**. S: **97/97 CLOSED; 7/7 roots CLOSED conditional on added (ab)/(ac) trust pending owner confirmation**. Unique functions and repeated TX occurrences are distinct units; overlapping assignments are never added to the global total.

The canonical [map](../../design/S1-S10-CLOSURE-MAP-20261026.md) defines subjects. Its initial Rc7 matrix is followed by Rc8/Rc9/Rc10 appendices on the SAME date; **Rc10 is the last superseding 2026-10-26 status**, including S6's historical scoped closure. [Rc7 inventory](../recount7-20261026/Rc7_premises.json) supplies the requested expanded row IDs; its retained list must not be mistaken for the later Rc10 retained list. This report preserves historical retirements, and grants no new retirement. The ledger frozen Rust revision is `'''+m['frozen_rust_revision']+'''`; NFK source revision is `'''+m['ledger_source_revision']+'''`. Historical proofs are not silently reassigned to this Rust revision.

[Row mapping](NFL_ROW_TO_CONE.json) records every occurrence, status, body hash, exact anchor or directed canonical call path, reason, slice membership, trust rows and support receipt references. [Builder](NFL_build.py) uses exact function IDs, not names resembling cone titles. Subject anchors are selected from canonical obligations and frozen inventory domains (not discovery search hits). Directed paths stay within TX1/TX2 and preserve the ledger's conservative target alternatives. Recursive/overapproximated graph membership is dependency coverage, not a semantic/refinement proof. S2 dispatch and S6 TX1 intentionally have broad descendant counts; **counts include their prerequisites**, distinguished from subject anchors. All source sites fall under S10; that does not supply its missing artifact/release obligations.

The [premise crosswalk](NFL_PREMISE_COVERAGE.json) exhausts all **32 raw Rc7 P rows**, including alias L185 and distinct native/global quantifier domains. It records candidate function sites and their status without asserting equivalence of a function packet to a full premise. No newly CLOSED ledger row is claimed to discharge an Rc7 Lnnn/Nnnn/F3Y_G_ family. Already-retired N and L primitive/preparation families receive support overlap only. In particular F3Y_G_ rows are P, not trust; local/native and global world/submission/Evidence domains stay distinct.

## Ten-cone matrix

The four columns retain the canonical 2026-10-26 format. Occurrence counts are **total / CLOSED / QUALIFIED / OPEN** and overlap across cones.

| Cone and canonical obligation | Exact ledger families | Discharging theorem / evidence and remaining boundary | Status |
|---|---|---|---|
'''
lines=[header]
for c,(title,families,status,blocker,theorems) in cones.items():
 n=m['cone_counts'][c]; count=' / '.join(str(n[k]) for k in ['total','CLOSED','QUALIFIED','OPEN'])
 lines.append(f'| **{c}** {title} | {families} | **{count}** occurrences. Historical: `{theorems}`. {blocker} | **{status}**; no change from final Rc10 status. |\n')
lines.append('''
## Per-cone assessment

Historical retirement support below is reused from the canonical dated appendices and [Rc10_059 receipt](../recount10-20261026/Rc10_059/receipt.json), with its stored #print axioms results. This is not a fresh check of those theorems or their complete statements. The audit does not claim a new theorem closure. The historical receipt's standard axioms are propext, Classical.choice and Quot.sound; its focused check is not L187/L188 completion.

''')
for c,(title,families,status,blocker,theorems) in cones.items():
 n=m['cone_counts'][c]
 relevant=[p for p in prem if c in p['cones']]
 retained=[p['id'] for p in relevant if p['disposition'].startswith('UNTOUCHED')]
 hist=[p['id'] for p in relevant if p['historical_receipt']]
 lines.append(f'### {c} — {title}\n\n')
 lines.append(f"Occurrences: {n['total']} total, {n['CLOSED']} CLOSED, {n['QUALIFIED']} QUALIFIED, {n['OPEN']} OPEN; {n['slice_occurrences']} intersect Q/S. Subject anchors: {', '.join(n['subject_rows']) or 'all 587 sites by definition'}; anchor statuses {json.dumps(n['subject_counts'],sort_keys=True)}. Anchors inside Q/S: {', '.join(n['subject_in_slices']) or ('all slice sites for S10' if c=='S10' else 'none')}.\n\n")
 lines.append(f'Family boundary: {families}. CLOSED occurrence support concerns the source cuts on recorded paths; it does not automatically discharge those families. Retained Rc7 P rows untouched by this refresh: {", ".join(retained) or "none specific to these historically retired families"}. Historical accepted P retirements, separately reused: {", ".join(hist) or "none"}. See the exhaustive crosswalk for candidate counts and quantifiers.\n\n')
 lines.append(f'Historical support: `{theorems}`. **Status change from the final 2026-10-26 Rc10 table: none.** {blocker}\n\n')
 if c=='S6':lines.append('Compared with the *initial* Rc7 matrix, L176/S6 had already changed at Rc8 via S6N, before this slice refresh. That accepted historical change is not slice-earned credit. The retained S6 CLOSED label is restricted to the accepted families and dictionary of that historical theorem, not every source/error site in NFK.\n\n')
lines.append('''## Untouched by the two slices

**No entire cone, counting its shared prerequisite footprint, is wholly outside both slices.** Every cone has shared arithmetic or source-site overlap; the JSON gives exact intersections. Claiming S8 is entirely outside is specifically false: TX1:195 and TX2:125 (`update_residue_row`) are CLOSED Q members.

**The principal subject roots of S1, S2, S3 and S9 are entirely outside both slices** under the explicitly listed anchor cuts. Their own roots receive no Q/S closure: S1 prepare/Prepared/claim, S2 native dispatcher/adapter/history, S3 pair/semantic endpoint, S9 factored Libra. For arithmetic cones the unaffected core is especially S3/S9; shared CLOSED field helpers do not close their law families. S8 accumulator construction, compact checker/expansion and final dot are outside, but residue traversal is partly inside. S10 artifact correspondence/release gates and S2 runtime association have no slice root at all. Thus “untouched since 2026-10-26” is justified for these obligations and the cone-status labels, not for every shared helper in an entire cone.

## Trust and promotion boundary

- **Added, pending owner confirmation:** RuntimeReturnData (ab), TX2:219 `emit_result`; RuntimeMemcmp (ac), TX2:226 `scan_proof_buffer`. Ledger CLOSED statuses are preserved conditionally; neither trust law is counted as discharged. Rejecting either reopens its root. Pool immediate-read/program-id/no-intervening-CPI return-data association stays OPEN.
- **Retained:** RuntimePersistence (ordinary data-byte two-transaction law, not runtime caller association); RuntimeSyscall / RuntimeSha256Value (reply value, not ordered request or experiment equality); Allocator/entrypoint/abort/rollback/library/SDK boundaries; P6/D188 option A / NativeContractSemanticTransport at exact source, feature, encoding, dictionary and tool pins. Trust reclassification is not removal of an implementation premise. P7 compiler/lowering trust remains behind historical L186 retirement.
- **D188 fidelity note:** canonical Rc9/Rc10 appendices retain rejected Parse-versus-panic divergence; both reject, but full Result equality must not be claimed. L166 still requires accepted Result/effects and both-reject/count-all-earlier-reads association. No quarantined or suspended Kani result is newly credited; no Kani verdict was produced or reclassified here.
- A promotion requires every remaining cone-era P row to be covered on its complete native/global domain by CLOSED composition or a cited accepted retirement, and exact source/artifact association. This mapping establishes no new such retirement. L154 budget and the joint non-vacuity fixture remain separate from cone counts. The security contract, constants, adversary, failure event and release target are unchanged.
''')
(D/'NFL_CONEMAP.md').write_text(''.join(lines))
g=['''# NFL slice-coverage gaps

**Numbers are status, not new credit. Target not yet established.**

A missing function counterpart is different from an OPEN counterpart. All occurrence assignments and frozen paths are in [NFL_ROW_TO_CONE.json](NFL_ROW_TO_CONE.json). All raw Rc7 P rows are in [NFL_PREMISE_COVERAGE.json](NFL_PREMISE_COVERAGE.json).

## Obligations without a ledger function row

| Obligation | Cone | Why it has no adequate row / next deliverable |
|---|---|---|
| L159 / alias L185 | S2; shared S7/S8 and whole experiment | Frozen3 StoredCarrierBinding quantifies over source/prover/runtime and complete physical history. No function occurrence is that runtime relation. Instantiate the same stored experiment and caller bytes, with an accepted source/model/history receipt. |
| L181 | S2/S10 and oracle-using joins | Full event-order/duplicate/early-exit/rejected-prefix probability-law transport has no single-function occurrence. Compose same runtime oracle experiment, retaining every earlier read. |
| L187 | S10 release gate | No coherent final frozen dependency replay is a Rust function row. Supply final root/closure/revision/toolchain/artifact receipt, exit/wall/RSS/swap and axioms. |
| L188 | S10 release gate | No release-wide trust/axioms/adoption/artifact audit is a Rust function row. Audit the exact final replay closure, including pending ab/ac and all source/dictionary/feature/tool instances. |
| L154 | External budget | Uniform total prover query bound, repeats included, is a condition on the adversary/work experiment, not verifier function coverage. Keep explicit; no new security credit. |
| Pool return-data association | S2/S6/S10 join | emit_result's conditional source closure is not the Pool immediate get_return_data/program-id/no-intervening-CPI execution. Provide the separate native Pool association. |
| Joint fixture / non-vacuity | Independent release gate | No occurrence demonstrates simultaneous inhabitation of all retained release premises on one physical two-transaction execution. |

## Function counterparts outside slice coverage

S8 is a **partial**, not complete gap: Accumulator::new TX1:174; compact check/row/semantic/value expansion TX1:096–099; finish_query_dot TX2:114 are OPEN outside Q/S. update_residue_row TX1:195/TX2:125 is already CLOSED inside Q. Historical L147 retirement is not completion of these later full native source packets. Likewise S1 prepare/Prepared/claim, S3 pair/semantic consumers, S9 factored root and S2 driver roots are outside; their exact row lists and remaining family meanings are in the cone report.

Q's geometry TX1:181/TX2:104 is QUALIFIED (headline import duplicates verifier.Phase; coherent retarget replay absent in pinned NFK). Four-dot roots and query-loop roots remain OPEN. CLOSED helpers cannot be promoted to full matching L143 or F3Y_G_L143. Distinct native/global quantifier domains remain a separate composition gap even where source candidates exist.

## No-cone rows and residual site coverage

**Rows belonging to no canonical cone: none (0/587).** S10 explicitly covers all source sites and continuations, so forcing a nonempty no-cone bucket would contradict its canonical scope. This does not make the S1–S9 subject cuts exhaustive. The following eight OPEN rows have no selected S1–S9 directed-anchor witness in this conservative graph and are assigned S10 only; this is an unresolved subject/caller-placement gap, not a proof that they are semantically unrelated to arithmetic or dispatch:

| Row | Function | Status |
|---|---|---|
''']
for r in rows:
 if r['row'] in m['only_S10_rows']:g.append(f"| {r['row']} | `{r['function']}` | {r['composed_status']} |\n")
g.append('''
Canonical callees are a conservative frozen inventory, including alternative receiver resolutions and recursion. Reaching a helper does not establish that every alternative executes or that a packet domain holds at every call. Conversely lack of a recorded path is a coverage gap, not proof of non-reachability. Subject roots and call paths are reviewable rather than inferred by name similarity.

## All Rc7 P rows: candidate sites versus absent quantified obligations

Historical accepted retirements are dated in the canonical Rc8/Rc10 appendices; no new retirement is made here. L185 is an alias; L134/L137 remain separate raw inventory rows even though the canonical later recount identifies their quarter predicate. Global families are independent from native-local ones.

| P row | Cone(s) | Candidate occurrence counts C/Q/O | Disposition |
|---|---|---|---|
''')
for p in prem:
 n=p['candidate_counts'];cnt='/'.join(str(n.get(k,0)) for k in ['CLOSED','QUALIFIED','OPEN']) if p['candidate_rows'] else 'no function counterpart'
 g.append(f"| {p['id']} | {'/'.join(p['cones']) or 'external'} | {cnt} | {p['disposition']} |\n")
(D/'NFL_GAPS.md').write_text(''.join(g))
print('reports built; 32 P rows:',len(prem))
