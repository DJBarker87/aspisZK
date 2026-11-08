from pathlib import Path
import json,lzma,subprocess,heapq
E=Path(__file__).resolve().parent
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
x=J(E/'NNL_LEDGER.json.xz');assert x['gate']=='PASS';a=J(E/'NNL_AUDIT.json');r=a['resources'];s=J(E/'NNL_SCAN.json');p=J(E/'NNL_PROVENANCE.json');v=J(E/'NNL_VALIDATION.json');by={q['row']:q for q in x['rows']};export=J(E/'NNL_EXPORT.json');cmp=J(E/'NNL_PREDECESSOR_COMPARISON.json');host=J(E/'NNL_GATE_INTEGRITY.json')
remaining={
'TX1:345':'328 is now CLOSED. NNG_FirstNative345.occurrence is support; complete emitted owned parent-to-canonical observation and original-input adapter/source association remain unproved. No345 candidate.',
'TX1:344':'CANDIDATE-FOLD NMV_CandidateRoots.root344 needs canonical345 at SAME implementation plus exact library/representation instantiation. ReviewedTranscription-TX1:344 retained, unused.',
'TX1:333':'CANDIDATE-FOLD NNF_Folds.process_tx1/NNF_TAS.roots needs both344 and240 at SAME implementation; same-function333/221 still needs both wrappers.',
'TX1:330':'CANDIDATE-FOLD NNF_Folds.entry_tx1 needs shared333/221 and both wrapper packets.',
'TX2:233':'No candidate: NMX_R3_Instantiated233 fills child/library schemas only. Actual Box cuts, complete emitted effects association and unrestricted all-Args port remain NMX_REV2_REMAINING items1–3.217/234 CLOSED do not prove the parent.',
'TX2:242':'Needs233 plus complete source/getter/Result/effect/domain derivation; no canonical candidate.',
'TX2:241':'Needs242 and SAME getter/range/encoder/native064 installation. Real NLG resume-extents clauses remain OPEN until241 closes; Root0 is a separate top occurrence obligation.',
'TX2:240':'CANDIDATE-FOLD NMV_CandidateRoots.root240 needs241 and exact library arguments. PoolLaws already CLOSED; no instantiated240 root. ReviewedTranscription-TX2:240 retained, unused.',
'TX2:221':'CANDIDATE-FOLD NNF_Folds.process_tx2/NNF_TAS.roots needs both344 and240; same-function333/221 needs both wrappers.',
'TX2:213':'CANDIDATE-FOLD NNF_Folds.entry_tx2 needs both wrappers through333/221.'}
assert {k for k,z in by.items()if z['status']=='OPEN'}==set(remaining)
text='Target not yet established. Twenty-first all-slices composition gate PASS:589 CLOSED /0 QUALIFIED /10 OPEN of599. Only094 and328 promoted.\n\n| Row | Exact remaining obligation |\n|---|---|\n'+''.join(f'| {k} | {remaining[k]} |\n'for k in sorted(remaining))
text+='\nAll60/60 authorized Lean/link/audit scopes used;0 Kani/0 extraction. The two assigned candidates have no remaining child/library/representation parameter. No authorized obligation is parked behind Kani. The ten remaining row candidates are external principal/fold work, not candidate deliverables assigned to this gate. No top field blocks a row’s CLOSED status.\n\nTop obligations remain separate in NNL_TOP_COMPOSITION.json: TOP:PoolLaws CLOSED; TOP:G0 OPEN. The2026-11-08 pointwise-inclusion strategy for condition(4) is recorded only, not proved here. Headline not composed. Source-to-ELF/L187/L188, cold release replay, extraction provenance/per-definition equalities, K086/(aj)(a), actual Pool execution and the top obligations remain open. Frozen3,L154,narrowedD188,100-bit per-attempt,privacy and two transactions unchanged.\n'
(E/'NNL_REMAINING.md').write_text(text)
def distance(start,target):
 lookup={(z['transaction'],z['function']):z['row']for z in x['rows']};h=[(int(by[start]['status']=='OPEN'),0,[start])];best={}
 while h:
  n,e,path=heapq.heappop(h);k=path[-1]
  if k in best:continue
  best[k]=(n,e)
  if k==target:return dict(open_members=n,edges=e,path=path)
  for f in by[k]['canonical_callees']:
   child=lookup.get((by[k]['transaction'],f))
   if child is None:continue
   if child not in best:heapq.heappush(h,(n+int(by[child]['status']=='OPEN'),e+1,path+[child]))
 raise AssertionError((start,target))
dist={b:distance(a,b)for a,b in[('TX1:330','TX1:094'),('TX1:330','TX1:136'),('TX2:213','TX2:115'),('TX2:213','TX2:217')]};(E/'NNL_DISTANCES.json').write_text(json.dumps(dist,indent=1)+'\n')
physical='Target not yet established. Twenty-first all-slices composition gate PASS: **589 CLOSED /0 QUALIFIED /10 OPEN of599**. Promotions only TX1:094 tx1 and TX1:328 first_decoded. No Pool promotion, edge removal or trust removal. Counts are composed function obligations, not security bits.\n\n'
for target,d in dist.items():physical+=' → '.join(k+' ['+by[k]['status']+']'for k in d['path'])+f". {d['open_members']} OPEN, {d['edges']} edges.\n\n"
physical+='094 is the complete revision4 RowSpec at LIB_Instances.VL/P and NNG_ProducerFull094.producer.087 is CLOSED at SAME original proof/public/scratch; entered-path R4 follows from SAME canonicalScan. F9 parseShape is total, preserving rejection outside proof57607. The full corrected prepare trace includes the digest dictionary.328 consumes this094 at SAME original arguments through NNG_Child328.original and the total carrier-lowering proof; full returned/error/ordered-log observations and formatter allocation abort relation remain. Only original observer=None/publicDom/P1880 clauses remain; P1880 propagates to345 and is discharged there by p1880_of_decode with the concrete decoder law. This does not close345.\n\n'
physical+='Native source provenance: actual frozen NMT_E001/E002 emissions, locks/LLBC/outputs/tools/spans and syntax-only compilation parameterization independently validated in NNL_EMISSION_REVIEW/NNL_SYNTAX_ASSOCIATION. Existing extraction trust narrowed by(bc) and used under(bm) is an explicit increased-reliance reclassification, not removal. Child graphs come from CLOSED roots; no free library/child/source-representation parameter remains. No new Kani/extraction or native multiplication credit.\n\n'
physical+=f"All{a['required_roots']} roots have complete standard-only raw ax2 walks, with the unchanged optimized binary and eight unchanged fidelity fixtures. Final NFX scan exit0 across{s['modules']} modules:0 dangling/duplicate owners/import mismatches; {s['cached_replicas']} identical serialized replicas retained separately. Four inherited collector disagreements retained; raw walk authoritative under(ab')(3)/(ax2). Initial L011 scan was FAILED with102 missing expected import entries; outer wrapper vacuity bug gave0 incorrectly. No credit from it. Fixed guard and source-derived entries pass at L060. L003/004 ordinary own review-input failures retained; L005/020 corrected exact checks pass. No timeout/OOM/cap increase or unchanged failed-shape replay.\n\n"
physical+='Rev4/(bs), rev3/(bq) and returned-value clarification, (bm)(bn)(bo)(bp)(br), allocator instantiation, split-B with Realizes/five binding conditions, approved state/query normalization and condition(4) pointwise-inclusion strategy are recorded. The last is not proved here. TOP:G0 OPEN; headline not composed. ReviewedTranscription-TX2:217 consumed as before;344/240 unused. All original trust statements/removal conditions, RuntimeClockSlotBinding owned-stage2 consumer, RuntimePersistence data-only, digest/error43/44 and quantified PDA38 remain. Phantom233→016/039 and240→043 edges retained/reclassified. Real NLG clauses stay OPEN pending241; Root0 separate.\n\n'
physical+=p['historical_verbatim']+'\n\nCurrent same-method conservative impact '+str(len(p['current_conservative_affected_CLOSED_rows']))+'/589 CLOSED rows. Fresh parent emissions do not reproduce every inherited child; no row reopened for provenance.\n\n'
physical+='Frozen crates/programs-r1/Cargo.lock4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Poolb936275465600469312d1f058cdc91ea2a11f3dc byte-identical. No shipped change or rebuild trigger. Inherited, not rebuilt: default '+x['pins']['default_elf']+'; devnet '+x['pins']['devnet_elf']+'; Pool '+x['pins']['pool_elf']+'. No cold release/source-to-ELF claim. No sibling/session-A worktree, wallet/key/account/fund/authority operation or push.\n'
(E/'NNL_PHYSICAL.md').write_text(physical)
base=J(E/'NNL_PLAN.json')['source_revision'];commits=subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True)
handoff=f'''Target not yet established. Twenty-first all-slices gate PASS: **589 CLOSED /0 QUALIFIED /10 OPEN of599**, ledger27 basis587/0/12. Only TX1:094 andTX1:328 promoted. Branch codex/cx-ledger28-20261107. No push.

094: `AspisR1.NNG_Candidate094.candidate` proves literal revision4 RowSpec_094 at LIB_Instances.VL/P and the ACTUAL emitted `NNG_ProducerFull094.producer`. It consumes CLOSED087 at SAME inputs, discharging R4 internally via SAME canonicalScan. F9 total parseShape closes the historical rejected-input finding. Full corrected preparation trace retains digest dictionary, source-order events, every Result/error/abort relation and native return. Only observer=None/publicDom/P1880 remain.

328: `AspisR1.NNG_Candidate328.candidate`, producer commit70c7bf7f7e9/L931, proves literal revision4 RowSpec_328 with SAME094 via `NNG_Child328.original` and total input lowering. No child/library/representation parameter remains. Full error formatter/log/abort relation retained. P1880 is a caller clause to345; canonical `p1880_of_decode` and concrete `NNG_P1880Discharge.decoder` discharge it there. This does not establish the missing345 parent association. NNG support is not another promoted row.

Actual frozen bodies verified independently from NMT_E001/E002 pins, LLBCs, source spans, complete output hashes and(bc) checks; syntax-only parameterization reproduces compiled Funs exactly. Increased(bm) reliance on the existing(bc)-narrowed extraction item is recorded as reclassification, never removal. All child/library fields are CLOSED graphs including LIB F9. Parent compile-source receipts and five selected object pins are checked in NNL_PARENT_COMPILE_PROVENANCE. Supplier source review resolves551 matching snapshots; one stale unused NNG_InstallRounds input is excluded, with no credit. Standard library/runtime/compiler/allocator/source-to-ELF and child trust retained; no cryptographic assumption, metric or game changed.

All{a['required_roots']} required roots raw ax2 standard-only ({a['new_roots']} new), same optimized raw binary `{a['same_optimized_proof_binary_sha256']}` and eight unchanged fidelity fixtures. Four inherited collector disagreements retained under(ab')(3)/(ax2). Current NFX scan exit0 across{s['modules']} modules: zero dangling/canonical duplicate owners/import mismatches; {s['cached_replicas']} identical serialized replicas retained. Every prior canonical row-root complete type/owner is identical. One explicitly repaired library lemma, LIB_VLib.parseShape_exact, now names the F9 total child. {len(cmp['changed_files'])} pinned revision4/F9 object replacements recorded; no other predecessor drift. L020 captures all current statements. The disjoint LIB_ParseShape094 context extension changes no implementation; pre-extension raw receipts remain valid and every new root is walked after extension.

60/60 serial capped Lean/link/audit scopes,0 Kani/0 extraction; optional16GiB scope unused. Every scope: ALL codex-* count<6, free>=40GB, admission exit0 AND allowed:true,6G high/8G max/no swap/tasks64, Lean-M7000, optimized link/walker. Outer wall{r['wall_seconds']:.3f}s, peak RSS{r['peak_rss_kib']}KiB, swaps0. Exact targets/commands/revisions/source/dependency/Aeneas pins/exits/wall/RSS/swaps/full print-axioms lines in ATTEMPTS and receipts. L003/004 were ordinary own review-input failures; corrected checks pass. L011 actual scan failed102 missing imports while outer wrapper incorrectly returned0 via an empty collector exception; it earns no credit. Strict guard plus committed-source import inventory pass at L060. Own scripts repaired only. No timeout/OOM/cap or timeout increase, unchanged killed-job rerun, or shared infrastructure edit.

Retained export `{export['export']}`; prepend to NNL_PATHS and import NNL_COMBINED_IMPORT. {host['selected_files_rehashed']} selected files and{host['imported_files_rehashed']} copied inputs rehashed; own cache/TMPDIR retained, zero deletions. Local validation: {v['compressed_sha_pairs']} compressed SHA pairs, {v['source_snapshots']} source snapshots,60 receipts,6 rejecting controls. Logs are losslessly archived; no file>20MB, object/binary/ELF or transient guard committed. One-line transcript summaries retained. Focused coherent cached composition, not a cold frozen-release replay.

Top records unchanged: TOP:PoolLaws CLOSED; TOP:G0 OPEN; headline not composed. Canonical rev4/(bs), rev3/(bq) and clarification, (bm)(bn)(bo)(bp)(br), rev2 superseded silent-return claim, split-B/Realizes/five conditions/state-query normalization and RZ-STATE carried. Owner2026-11-08 condition(4) pointwise-inclusion strategy is RECORDED ONLY, not proved here. Allocator is statement instantiation, not success trust. ReviewedTranscription-TX2:217 remains consumed;344/240 remain unused by CLOSED rows. Phantom edges retained/reclassified, real NLG extents clauses OPEN pending241, Root0 separate. RuntimeClockSlotBinding owned-stage2 consumer unchanged; K086/(aj)(a) PENDING. Frozen3,L154 statement parameter,narrowedD188,100-bit PER-ATTEMPT,privacy,two transactions unchanged. Digest/error43/44, PDA38 quantified, RuntimePersistence data-only.

{p['historical_verbatim']}

Historical line verbatim. Current conservative same-method impact{len(p['current_conservative_affected_CLOSED_rows'])}/589 CLOSED rows; new-row unresolved blob counts{ {k:len(z)for k,z in p['new_rows_hits'].items()} }. No row reopened. Fresh actual parent provenance does not reproduce all reused children. Extraction per-definition provenance, cold release replay/L187/L188/source-to-ELF, actual Pool execution, the ten rows and top obligations remain. See NNL_REMAINING member by member. No assigned candidate obligation remains parked behind Kani; whole60-scope budget used.

Frozen source and inherited ELF pins are in NNL_FROZEN_SOURCE_CHECK / NNL_PHYSICAL. Byte-identical verifier4bb3b3f51e16 and Poolb936275465; no rebuild trigger. Default f8c0ec72…/devnet63ad3e9c…/Pool e0e49c34… are inherited, not rebuilt. No sibling/session-A worktree or key/account/fund/authority action.

Read NNL_LEDGER.json.xz (+original SHA), DELTA, CANDIDATE_REVIEW, CLAUSE_REVIEW, EMISSION_REVIEW, SYNTAX_ASSOCIATION, AUDIT, SCAN, PHYSICAL, REMAINING, TOP_COMPOSITION, PROVENANCE, VALIDATION and ATTEMPTS. Pre-final stage commits:

{commits}
Final evidence commit is the revision containing this handoff. No push.
'''
(E/'NNL_HANDOFF.md').write_text('')
for paragraph in handoff.split('\n\n'):
 with(E/'NNL_HANDOFF.md').open('a')as f:f.write(paragraph+'\n\n')
(E/'NNL_HANDOFF.md').write_text((E/'NNL_HANDOFF.md').read_text().rstrip()+'\n')
lines=['Preflight and failed shapes are retained; each scope summary below links to its complete receipt.']
for q in sorted(E.glob('NNL_L*/receipt.json')):
 d=J(q);lines.append(f"{d['attempt']} {d['kind']} {d['module']}: exit={d['exit_status']} wall={d['wall_seconds']:.3f}s RSS={d['peak_rss_kib']}KiB swaps={d['swaps']} revision={d['source_revision']} receipt={q.parent.name}/receipt.json")
(E/'NNL_TRANSCRIPT.txt').write_text('\n'.join(lines)+'\n')
print('NNL handoff/physical/remaining written; target not yet established')
