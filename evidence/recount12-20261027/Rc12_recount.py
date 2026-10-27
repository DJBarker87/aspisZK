"""Recount checked atomic families; report release obligations without adoption."""
from pathlib import Path
import copy, hashlib, json, re, subprocess
E=Path(__file__).resolve().parent
R=E.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads((R/p).read_text())
def save(n,x): (E/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def norm(s): return re.sub(r'\s+',' ',s).strip()
b=read('evidence/recount10-20261026/Rc10_premises.json')
a=read('evidence/recount11-20261027/Rc11_premises.json')
receipt=read('evidence/recount12-20261027/Rc12_001/receipt.json')
assert receipt['exit_status']==0
fresh=(E/'Rc12_001/stdout.log').read_text()
assert 'error:' not in fresh
nf=norm(fresh)
# Complete retained printed blocks, not theorem-name or binder-count heuristics.
split=r'(?m)(?=^(?:structure |def |theorem |@\[|@Aspis|\x27Aspis|AspisR1\.))'
checks=[]
for src in ['evidence/recount11-20261027/Rc11_002/stdout.log']:
    blocks=[x for x in re.split(split,(R/src).read_text()) if x.strip()]
    matches=[norm(x) in nf for x in blocks]
    assert all(matches), [i for i,m in enumerate(matches) if not m]
    checks.append(dict(path=src,sha256=sha(R/src),printed_blocks=len(blocks),all_match=True))
pins=read('evidence/recount11-20261027/Rc11_statement-check.json')
for root,key,statement in [('Rc10_Top','source_before_sha256','Rc11_BEFORE.lean.txt'),('ARX_Root','source_after_sha256','Rc11_AFTER.lean.txt')]:
    assert sha(R/'lean'/f'{root}.lean')==pins[key]
    old=(R/'evidence/recount11-20261027'/statement).read_text()
    assert norm(old).removeprefix("@") in nf, root
    (E/f'Rc12_{root}.BEFORE.lean.txt').write_text(old)
    (E/f'Rc12_{root}.AFTER.lean.txt').write_text(old)
    assert f"'AspisR1.{root}.deployed' depends on axioms: [propext, Classical.choice, Quot.sound]" in fresh
save('Rc12_statement-check.json',dict(inventory=checks,source_hashes_unchanged=True,complete_retained_root_types_in_fresh_output=True,before_after_identical_per_root=True,cross_root_identity_claimed=False,adoption=False))
# Verify the exact cohort receipts, without replaying the unchanged package.
cohort=read('evidence/l188-audit1-20261027/L8a_CohortReceipts.json')
for p in cohort:
    assert sha(R/p['path'])==p['sha256']
    assert (R/p['path']).stat().st_size==p['bytes']
save('Rc12_COHORT_PINS.json',dict(receipts=cohort,objects=read('evidence/l188-audit1-20261027/L8a_HostPins.json'),scope='RPz8 selected cohort only; cohort = release extraction still depends on D188-P/P2',fresh_host_object_rehash=False))
X='evidence/extraction-repro5-20261027/XRe_OBLIGATIONS.md'
C='evidence/extraction-repro5-20261027/XRe_CORRESPONDENCE.md'
D='docs/research/100bit-spend-path-20261013/design/D188-PROVENANCE-FINDING-20261027.md'
items=[
('ExtractionCallClosure','L186–188, L157/L181; prerequisite of all association items','Call-closed pinned release kit including the required Iterator::copied library call; valid release Types/Funs and external-library mapping/hash inventory.'),
('SemanticPublicHashDictionaries','L080–082/L139–146/L157/L181','Actual release dependency carriers, dictionaries, nested Result/error and ordered effects associated with historical inlined carriers; semantic_boundary call remains blocked.'),
('PreparedScratchProjection','L122–124/L130–132/L139–141/L157/L181; S1 installed preparation','SAME sem/view/hash, arbitrary initial scratch29; early failures and successful powers29(gamma) overwrite; SAME gamma/kappa as prepared_claim.'),
('PreparedClaimPowersAssociation','L139–141/L144–146/L157/L181; S1','Old gamma versus successful 29-entry powers array, six selections, seven parts, kappa powers, Dot bounds and all errors/effects; no whole-body pass.'),
('QueryGeometryLineInvariant','L130–132/L149–150/L157/L181','Start/inverse projection and line_z cache at each reached query, including failed range/zero-inverse construction and effects.'),
('DotCountProjection','L128/L142/L147–148/L157/L181; S5 association','Actual canonical Dot, count erasure, no-wrap 4096-term invariant, push/finish, limb canonicality and failure/ownership frame.'),
('BatchedWeightsQueryLoop','L125/L128/L142–143/L147/L149–150/L157/L181; S7/S8','SAME ordered queries/accumulator, eager/deferred weights, restoration and failure/state/effect association. K020 serialization is not this arithmetic law.'),
('AcceptedCandidateCheckpoint','L091–109/L122–124/L130–132/L139–141/L149–150/L157/L159/L180–188; S1','Accepted candidate.tx1 at SPLIT versus retired dispatch: physical compact bytes, binary authentication, SAME saved CP, ordered effects and charged rejected prefixes; allocator/Vec/result frames remain.'),
('VerifyObservedAssociation','L144–146/L157/L181','Actual semantic_rounds/verify_finish, earlier rejects and ordered effects, rather than opaque successful semantic return.')]
leafs=[
('check_values','Full loop/iterator/canonical byte association at caller bounds; K008 only lengths 0..31, full 464 timed out; preserve ignored tail.'),
('echeck','Full source loop/carrier/error association; K013 only 0..63 and both flags; 928/224 timed out.'),
('expand_values','Full caller bounds, overflow/borrow/frame and byte/Result association; K019 only SAME 32/64 bounds, arbitrary destination index; 464/928 timed out.'),
('wide_view','Whole Result/borrow/slice/error/field association; actual 57607/13831/928 harness timed out.'),
('checkpoint','Whole source-to-reference-to-Lean checksum/payload/Vec/allocator/Result and ordered-effects certificate; passing serialization fragments insufficient; K020 timed out.'),
('prepared_claim','Whole shipped-to-owned-reference-to-Lean arithmetic/state/encoding/Result/effect certificate; whole/powers/selection harnesses timed out.')]
new=[]
for i,(name,families,obligation) in enumerate(items):
    new.append(dict(id=f'Rc12_D188P2_A{i}',name=name,classification='P',owner='lead',scope='deployment only',status='open',affects=families,obligation=obligation,evidence=[X,D],counted=True,kind='association artifact prerequisite' if i==0 else 'model/release association'))
for name,obligation in leafs:
    new.append(dict(id=f'Rc12_D188P2_leaf_{name}',name=f'P6 whole leaf: {name}',classification='P',owner='lead',scope='deployment only',status='open',affects='L099/L108–109/L139–148/L157/L181/L186–188 (XRe collective leaf-family inventory; per-leaf carrier mapping in XRe_CORRESPONDENCE.md)',obligation=obligation,evidence=[X,C,D],counted=True,kind='whole source/reference/model leaf certificate',overlap='prepared_claim overlaps A3; checkpoint overlaps A7; leaf body certification and old/release interface transport are separate deliverables, not independent probability terms'))
assert len(new)==15
updates=[
 dict(id='L187',classification='P',owner='lead',status_before='open',status_after='closed for RPz8 cohort only',delta_P=-1,evidence=['evidence/replay-dry9-20261027/RPz8_HANDOFF.md','evidence/l188-audit1-20261027/L8a_HANDOFF.md','Rc12_COHORT_PINS.json'],remaining='Cohort = release extraction depends on D188-P/P2; historical/fresh cached kernel comparison remains unestablished.'),
 dict(id='L188',classification='P',owner='lead',status_before='open',status_after='open: F-CONTRACT and D188-P',delta_P=0,evidence=['evidence/l188-audit1-20261027/L8a_TrustAudit.md',D],remaining='Named contract trust-inventory reconciliation and producer provenance; import-only F-AXIOM finding retained, no new trust accepted.'),
 dict(id='L186',classification='P',owner='lead',status_before='already closed in Rc10/Rc11 baseline',status_after='confirmed closed for artifact reproduction',delta_P=0,evidence=['evidence/elf-repro1-20261027/ELa_RESULT.md','evidence/elf-repro1-20261027/ELa_build_manifest.json'],remaining='No duplicate credit: pins/recipe reproduced under retained P7; D188 model association remains in new rows.'),
 dict(id='L166',classification='P',owner='lead',status_before='open',status_after='open',delta_P=0,evidence=['evidence/l166-proof5-20261027/BEm_HANDOFF.md','design/PREMISE-LEDGER-20261025.md'],remaining='Whole shipped-body Result/ordered-log certificate on SAME reached input, slot, backend state and before-history: BEl_PhysicalCut.transfer bridge satisfying BEh_Scope.Law against BEl_NativeBatchCut.native. Reference interpreter alone insufficient. Alternative trace-fidelity reading of D188 requires an explicit lead/owner ruling covering this bridge; no such discharge assumed. Rejected prefixes must reject and charge all earlier reads; Err(Parse) versus fail panic retained.')]
for r in new: updates.append(dict(id=r['id'],classification='P',owner='lead',status_before='not enumerated',status_after='open',delta_P=1,evidence=r['evidence'],remaining=r['obligation']))
def count(rows): return {c:sum(r['classification']==c for r in rows) for c in 'TPGC'}
def totals(rows):
    return {scope:count([r for r in rows if r['scope']==scope]) for scope in ['actual antecedent','deployment only','deployment alias']} | {'deployment-inclusive non-alias':count([r for r in rows if r['scope']!='deployment alias']),'raw including alias':count(rows)}
roots={}
for root,old in [('Rc10_Top',b['rows']),('ARX_Root',a['rows'])]:
    updated=copy.deepcopy([r for r in old if r['id']!='L187'])+copy.deepcopy(new)
    for r in updated:
        r['status']='open' if r['classification']=='P' else 'retained'
        if r['id'] in ['L166','L188']: r['Rc12_update']=next(u for u in updates if u['id']==r['id'])
    before,after=totals(old),totals(updated)
    assert before['actual antecedent']==after['actual antecedent']
    assert after['deployment-inclusive non-alias']['P']-before['deployment-inclusive non-alias']['P']==14
    roots[root]=dict(theorem=f'AspisR1.{root}.deployed',adopted=root=='Rc10_Top',before=before,after=after,rows=updated)
assert roots['Rc10_Top']['after']['actual antecedent']==dict(T=83,P=12,G=13,C=0)
assert roots['ARX_Root']['after']['actual antecedent']==dict(T=83,P=11,G=13,C=0)
assert roots['Rc10_Top']['after']['deployment-inclusive non-alias']==dict(T=89,P=30,G=13,C=0)
assert roots['ARX_Root']['after']['deployment-inclusive non-alias']==dict(T=89,P=28,G=13,C=0)
result=dict(method='Rc11 atomic law families; split conjunction leaves, preserve SAME existential witnesses, guards and installation slots; no Fin22 multiplication; native/global finish laws distinct; returned facts/data not premises; L185=L159 excluded from distinct totals. New deployment rows enumerate distinct requested artifact/correspondence tasks, not additional Lean hypotheses or independent probability losses.',roots=roots,changes=updates,actual_premise_delta=dict(T=0,P=0,G=0,C=0),deployment_inclusive_delta=dict(T=0,P=14,G=0,C=0),new_deployment_rows=new,adoption=False,authoritative_ledger_edited=False,contract_edited=False)
save('Rc12_LEDGER_DELTA.json',result)
# Pin all external evidence consumed by this packet; no binaries copied.
paths=[X,C,D,'design/PREMISE-LEDGER-20261025.md','docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md','docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md','evidence/recount10-20261026/Rc10_premises.json','evidence/recount11-20261027/Rc11_premises.json','evidence/recount11-20261027/Rc11_LEDGER.md','evidence/l188-audit1-20261027/L8a_HANDOFF.md','evidence/l188-audit1-20261027/L8a_TrustAudit.md','evidence/l188-audit1-20261027/L8a_HostPins.json','evidence/elf-repro1-20261027/ELa_RESULT.md','evidence/elf-repro1-20261027/ELa_build_manifest.json','evidence/l166-proof5-20261027/BEm_HANDOFF.md','evidence/l188-audit1-20261027/L8a_StatementComparison.json','lean/Rc10_Top.lean','lean/ARX_Root.lean']+[x['path'] for x in cohort]
save('Rc12_INPUT_PINS.json',[dict(path=p,sha256=sha(R/p),bytes=(R/p).stat().st_size) for p in sorted(set(paths))])
lines=['# Rc12 mechanical recount','', '**The deployed 100-bit target is not yet established.** Rc10 remains adopted; ARX remains an unadopted candidate. No proof, theorem premise removal, adoption or authoritative ledger/contract edit. The deployment-inclusive P count increases by **14** for each root.','', '## Method and complete before/after statements','',result['method'],'', 'The single fresh `Rc12_Audit` print checks the complete retained root types and every expanded Rc11 inventory block (Rc12_statement-check.json). Each root’s complete BEFORE/AFTER files are identical. The root sources match Rc11 byte hashes. This is a new mechanical recount and focused cached audit, not an unchanged package replay. The RPz8 coherent replay is reused by pinned receipts, separately from this SInt2-cache print. The complete universe/kernel Expr evidence remains pinned through L8a_StatementComparison.json and RPz8 receipts; no historical cached-kernel equality is asserted.','', '| Basis | Rc10 before → after T/P/G/C | ARX candidate before → after T/P/G/C |','|---|---|---|']
fmt=lambda v:'/'.join(str(v[c]) for c in 'TPGC')
for scope in roots['Rc10_Top']['before']:
    vals=[fmt(roots[r]['before'][scope])+' → '+fmt(roots[r]['after'][scope]) for r in roots]
    lines.append(f'| {scope} | '+ ' | '.join(vals)+' |')
lines+=['','Actual deltas: **0/0/0/0** for both roots. Deployment delta: **0/+14/0/0**, exactly L187 −1 plus fifteen newly enumerated obligations +15. L186 was already absent: confirmation earns zero additional credit. L185 aliases L159 and adds one raw P only in Rc10. Candidate-versus-adopted differences remain −1 actual P (L159), −2 distinct inclusive P (L159 and L181), −3 raw P including L185. None is credited as adopted progress.','', 'L154 remains P/external in this requested frozen Rc11 comparison (83/12/13 and 83/11/13). The older C3-BIN proposal to classify it G is not applied here; applying it separately would move one P to G per root and would be reclassification, not discharge. No query-budget law is removed.','', '## Deployment ruling rows','', '| ID | Disposition | Evidence and exact qualification |','|---|---|---|']
for u in updates[:4]: lines.append(f"| {u['id']} | {u['status_after']} (P delta {u['delta_P']:+}) | {'; '.join(u['evidence'])}. {u['remaining']} |")
lines+=['', 'L187 cohort pins are Rc12_COHORT_PINS.json: Rc10 4,963 green repository modules, ARX 5,259, union 5,260; zero failed/unbuilt/unresolved. Full source and receipt hashes are retained, including object hashes e41293c7… (Rc10), e627f8a4… (ARX). Closure of this cohort does not prove **cohort = release extraction**. That dependence remains D188-P/P2, tracked by L188 and the new rows; it does not reopen the unchanged replay task.','', 'L186 artifact pins reproduced by ELa: default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`. Exact recipe/compiler/source census is pinned in ELa_build_manifest.json. These are reused fresh reproduction receipts, not builds run by Rc12.','', '## New D188-P2 deployment obligations','', 'All rows below are **P / lead / deployment only / open**, +1 each, present for both roots. Identifiers are local to this packet; they do not allocate authoritative L-numbers. The “affects” columns identify threatened attribution families, including historically retired rows; they do not reinstate those as actual antecedents or multiply the count by affected-family cardinality.','', '| Local ID | Required certificate | Affected ledger families |','|---|---|---|']
for r in new: lines.append(f"| {r['id']} / {r['name']} | {r['obligation']} | {r['affects']} |")
lines+=['', f'All items 0–8 are from `{X}`; six leaf details from `{C}`. ExtractionCallClosure is an artifact prerequisite, not a seventh translator-failing release leaf. The six leaves are check_values, echeck, expand_values, wide_view, checkpoint and prepared_claim. The leaf-family mapping is collective where XRe does not provide a per-leaf L-number assignment; no finer attribution is invented.','', 'Association A3 and leaf prepared_claim, and A7 and leaf checkpoint, overlap in work but specify different certificates: old-model/release-interface transport versus whole release-body/reference/Lean correspondence. Leaf closure supplies inputs to association; association alone does not certify the leaf body. One certificate may close multiple tasks, with that overlap recorded; no duplicate probability loss or security bits are added. These are fifteen enumerated deployment tasks, not a claim of fifteen new logically independent theorem antecedents.','', '## Actual families and unchanged semantics','', 'Every actual row and retained release row, with the inherited exact family/definition/guards/owner, is in Rc12_LEDGER_DELTA.json. Native L142–L146 and global F3Y_G_L142–L146 remain ten independent P families; L154 remains one. Rc10 also retains L159. ARX removes that input by defining its induced P and admitted runtime observer; L181 is absent for that candidate and L185 follows its alias. Quantifiers, carrier types, failure-event constructor and conclusion schema have not changed in this recount. ARX’s admitted observer is not equated to arbitrary unfiltered runtimes; outside-admission outcomes are zero-extended without renormalizing, while issued rejected-prefix costs remain charged. L081 remains the global fixed-root P1 antecedent; success/query-restricted coverage does not silently discharge it.','', '## Non-vacuity and validation','', 'No new joint inhabitant is constructed. ARX_Nonvacuity.conditional retains SAME installed SupportedEntry and consistent native/H cylinder gates; RPz8 FIn_Nonvacuity.witness_or_collision, FIo_Nonvacuity.arithmetic_fixed/same_result and Parsed Phase are conditional/local witnesses. Separately passing real-byte stages do not jointly inhabit every root premise. See pinned RPz8_NONVACUITY.md and Rc11_LEDGER.md.','', f"One Lean attempt of 10, 0 Kani: `Rc12_Audit`, exit {receipt['exit_status']}, wall {receipt['wall_seconds']} s, peak RSS {receipt['peak_rss_kib']} KiB, swaps {receipt['swaps']}, source revision `{receipt['source_revision']}`. Full command, source/dependency hashes, actual scope limits and printed axioms: Rc12_001/receipt.json, stdout.log, time.log and scope receipt. Both roots print exactly propext, Classical.choice, Quot.sound. No new theorem; no additional #print obligation. One scope, MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64, -M7000; zero retries, timeouts or memory kills.",'', 'Only Rc12-prefixed audit/evidence changes; no shipped/cfg(kani)/wallet changes, Rust/SBF build, package replay, push, adoption, ledger edit or contract edit. Remaining nine compile attempts are unused because the mechanical task is complete; no proof job was authorized by the resume.']
(E/'Rc12_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({r:{'before':d['before'],'after':d['after']} for r,d in roots.items()},indent=2))
