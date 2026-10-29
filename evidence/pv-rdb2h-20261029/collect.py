"""Validate replay evidence and publish scoped dispositions; never launch a compiler."""
from pathlib import Path
import hashlib,json,re,subprocess

E=Path(__file__).resolve().parent
G=E.parent/'pv-rdb2g-20261029'
F=E.parent/'pv-rdb2f-20261029'
p=json.loads((E/'plan.json').read_text())
cmp=json.loads((E/'comparison.json').read_text())
standard={'propext','Classical.choice','Quot.sound'}
rs=sorted((json.loads(q.read_text()) for q in E.glob('lean-*/receipt.json')),key=lambda x:x['attempt'])
prior=sorted((json.loads(q.read_text()) for q in G.glob('lean-*/receipt.json')),key=lambda x:x['attempt'])
assert len(rs)<=60
assert not (E/'refusals.jsonl').exists(), 'refusals require explicit reporting'
available=set(p['reused_completed_order'])
all_modules={x['module'] for x in p['objects']}
build=set(p['build_order'])
for r in rs:
    assert r['exit']==0 and r['matches_rdb2f'],r['module']
    assert 64300<=r['attempt']<=64399
    for dep in r['imports']:
        assert dep['module'] not in build or dep['module'] in available,(r['module'],dep['module'])
    available.add(r['module'])
    for which in ['admission-before.json','admission-launch.json','admission-barrier.json']:
        assert json.loads((E/f"lean-{r['attempt']}"/which).read_text())['allowed'] is True
    assert r['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
    assert int(r['swap'])==0
    assert '7000' in r['target']
    for line in r['print_axioms']:
        match=re.search(r'depends on axioms: \[([^\]]*)\]',line)
        if match:assert {x.strip() for x in match[1].split(',') if x.strip()}<=standard,line
remaining=[m for m in p['build_order'] if m not in available]
assert not remaining and len(rs)==48 and len(prior)==40
assert cmp['rebuilt']==88 and not cmp['missing_rebuilds']
assert not cmp['object_differences'] and not cmp['rebuilt_dependency_mismatches']
audits=[]
for new,old,m,count in [(64397,63397,'StatementAudit',137),(64398,63398,'AxiomsAudit',137),(64399,63399,'FocusedReplay',80)]:
    r=next(r for r in rs if r['attempt']==new)
    assert r['module']=='R1Z.PV_RDB2F_'+m
    output=(E/f'lean-{new}/output.log').read_bytes()
    original=(F/f'lean-{old}/output.log').read_bytes()
    assert output==original,('audit output differs',m)
    if m!='StatementAudit':assert len(r['print_axioms'])==count
    audits.append(dict(attempt=new,module=r['module'],exit=r['exit'],wall=r['wall'],peak_rss_kib=r['peak_rss_kib'],swap=r['swap'],source_revision=r['source_revision'],execution_revision=r['execution_revision'],output_sha256=hashlib.sha256(output).hexdigest(),output_identical_to_rdb2f=True,declarations=count,print_axioms=r['print_axioms']))
native=[json.loads((E/n/'receipt.json').read_text()) for n in ['preflight','final-fingerprint']]
assert len(native)<=5 and all(r['exit']==0 and int(r['swap'])==0 for r in native)
summary=dict(branch='codex/pv-rdb2h-20261029',base=p['revision'],worktree='/Users/dominic/ZK/.worktrees/pv-rdb2e',restored=['V256','V257'],suspended=['V231'],evidence_class='class B; structural (K-1 substitute) under own-1; V370/D381/D386 retained',V231='software path proved; SHA-NI path conditional on R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics, pending owner item 3',lean=dict(used=len(rs),limit=60,passed=len(rs),reused_rdb2g=len(prior),complete_replay=len(rs)+len(prior),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swap=0),native=dict(used=len(native),limit=5,kani=0,native_regressions=0),attempts=rs,reused_attempt_receipts='../pv-rdb2g-20261029/combined-audit.json',native_scopes=native,audits=audits,object_differences=cmp['object_differences'],required_remaining=remaining,new_proofs=0,source_edits=0,endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_changed=0)
(E/'combined-audit.json').write_text(json.dumps(summary,indent=2)+'\n')
for row in ['V256','V257']:
    details=('original gamma reverse iterator, raw current-array handles, FnMut capture, every reverse write, first and optional second carry, decode, and actual verifier scalar/trace continuation' if row=='V256' else 'original ordinary reverse iterator, current-array handles, FnMut quotient capture, all eight from_fn writes, final captured quotient read, decode, and actual verifier scalar/trace continuation')
    (E/(row+'.md')).write_text(f'''# {row} — RESTORED

Evidence class: class B; **structural (K-1 substitute)** under own-1. Compiler preservation V370 and the pending D381/D386 compiler-cohort boundary remain retained.

Before: source laws proved, but restoration suspended on the incomplete exact-environment consumer/audit replay. After: that replay gate is discharged. The inherited laws bind the {details}. The [statement-by-statement source binding](../pv-rdb2f-20261029/own1-binding.json) and [source-law evidence](../pv-rdb2f-20261029/{row}.md) are unchanged; this report supersedes their exact-environment suspension only.

All 88 targets pass in the literal original environment: 40 verified RDB2G objects reused, 48 remaining targets freshly elaborated here in dependency order. Every rebuilt object hash matches rdb2f. Statement audit64397, axioms audit64398 and focused replay64399 pass, with byte-identical output to rdb2f. The axiom audit covers137 declarations; the focused replay covers80 theorems. All axiom results use only the permitted standard subset. See [combined audit](combined-audit.json), [comparison](comparison.json) and [report](REPORT.md).

No new proof, extraction or native regression was run. Inherited native differentials remain finite validation; universal source laws retain their structural evidence class. No source-to-machine-code or privacy-endpoint closure is added. Compiler/Aeneas/Rust agreement is reclassification within existing tool trust, never premise removal. Endpoint premises removed0, added0, changed0. T remains exactly entropy_law, entropy_kernel, observation. Privacy target not yet established.
''')
(E/'V231.md').write_text('''# V231 — SUSPENDED, unchanged

Software path proved; SHA-NI path conditional on `R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics`, pending owner item 3. The unchanged SHA modules were replayed as prerequisites of the frozen combined audits. This discharges no instruction-semantics hypothesis or owner decision. No new SHA proof or native regression was run. [Inherited scope and evidence](../pv-rdb2f-20261029/V231.md).
''')
table='\n'.join(f"| `{r['module']}` | {r['attempt']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swap']} | {r['source_revision'][:10]} | "+('137 statements; axioms checked64398' if r['attempt']==64397 else f"{r['declarations']} permitted-standard-subset results")+' |' for r in audits)
(E/'REPORT.md').write_text(f'''# RDB2H — D445 completed exact-environment replay

**V256 and V257 RESTORED: class B, structural (K-1 substitute) under own-1. V370/D381/D386 compiler preservation retained. V231 unchanged: software path proved; SHA-NI conditional on `R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics`, pending owner item 3. Privacy target not yet established.**

Branch `codex/pv-rdb2h-20261029`, base `{p['revision']}`; exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-rdb2e`. Only this directory's evidence and replay orchestration were added. No Lean/Rust source, standing launcher, dictionary, simulator, observer, T, production code or soundness-file edits; no new proofs, extraction, Kani, native regression, push/merge or wallet/key activity.

## Exact environment and completed closure

[Preflight](preflight.json) verifies the original Env-J JSON exactly, Lean4.32.0 executable and unchanged run2.py hashes, all178 pinned source hashes, all5,673 external object hashes, and130 retained objects with their source/import/companion cohort. The leading literal LEAN_PATH remains `/home/dombarker/project-offloads/codex-pv-rdb2e-20261029/lean-objects`; the original runner's duplicated leading prefix is preserved. Sources remain at the existing rdb2f source root; no corpus copy or shared source write occurred. Preflight found no64300–64399 collision.

All48 remaining modules were freshly elaborated unchanged in dependency order, including removed prerequisites, every remaining consumer, statement audit64397, axioms audit64398 and focused replay64399. Together with the40 verified RDB2G objects, this completes all88 targets, including the30-module original R72 closure. The90 unaffected cache objects remain verified. [Comparison](comparison.json) and [final fingerprint](fingerprint.json.xz) show **88/88 rebuilt objects identical to rdb2f, zero differences, zero missing targets, zero dependency mismatches**. Every178 project source and5,673 external object hash remains unchanged. R72 Funs remains `ebeff6a2d06be7402afd468206e5542d15bea07d36b06f26412da992af0f052a`; its source remains `b693c4bc5c00835a3f0fe3ff2b895ce58f40c6a52cf6cfdfdac7beacde8e000e`.

The frozen statement audit output is byte-identical to rdb2f across137 declarations. The axiom audit's137 results and focused replay's80 theorem results are also byte-identical and use only propext, Classical.choice and Quot.sound (or no axioms). These are unchanged source/model consumer gates, not a full privacy-endpoint replay.

## Dispositions and retained boundaries

[V256](V256.md): original gamma iterator/FnMut/current-array/caller association source laws are restored after the exact-environment suspension is discharged. Every changing reverse write, returned quotient, first and optional second carry, decode, and actual verifier scalar/trace continuation retain the inherited structural binding.

[V257](V257.md): original ordinary iterator/from_fn/final quotient/caller association source laws are restored after the same gate. All eight writes and final captured quotient read precede decode and the actual verifier continuation. The original verifier route remains distinct from the indexed prover route.

Evidence class for both is **class B; structural (K-1 substitute)** under own-1, with [inherited binding](../pv-rdb2f-20261029/own1-binding.json), universal Lean source laws and existing native checks at their original **finite-validation** class. Source-to-machine-code preservation V370 and pending D381/D386 remain named obligations. Compiler/Aeneas/Rust agreement is reclassification within existing tool trust, never premise removal.

[V231](V231.md) remains suspended pending owner item3; replay does not discharge the SHA-NI semantics hypothesis. Endpoint theorem and premises removed0, added0, changed0; only V256/V257's evidence dispositions change. T remains exactly entropy_law, entropy_kernel, observation. Runtime/allocator primitive adequacy under rdea-1, actual handlers/runtime, E1/E2, real RunJoin, proof-account routing and L1/L2/L3 retain their obligations.

## AGENTS.md section6 receipts

**48/60 Lean attempts, all exit0; 2/5 capped evidence/native scopes, both exit0; Kani0.** Lean IDs64300–64344 and64397–64399 only. Peak Lean RSS {summary['lean']['peak_rss_kib']:,}KiB; all swaps0. Every scope requires same-shell admission exit0 plus allowed:true and an allowed in-scope barrier, with MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64 and Lean-M7000. One scope and one module at a time. No refusal, timeout, memory kill, void admission, failed theorem or unchanged failed-proof rerun occurred.

| Exact target | Attempt | Exit | Wall | Peak RSS KiB | Swap | Source revision | Axioms result |
|---|---:|---:|---:|---:|---:|---|---|
{table}

[Combined audit](combined-audit.json) records each exact command, target, source revision/blob/hash, execution revision, import fingerprint, exit, wall, RSS, swap and full emitted axioms lines, plus raw receipt paths. Modules without an emitted axioms query receive no standalone aggregate-axiom claim; the frozen audits cover the declared consumer manifest. The40 earlier attempt receipts remain in [RDB2G](../pv-rdb2g-20261029/combined-audit.json). [COMMITS.txt](COMMITS.txt) records path-limited stages; the final report commit follows that snapshot.

The verified original-path cache is retained for dependent work, explicitly authorized as the continuation. No other job's outputs or sources were removed; no binaries, Cargo targets or compiled objects are committed. Every committed file is below20MB. No further compiler runs are needed for this completed replay; the remaining budget is unused because the requested gate is fulfilled.

Next: consume the restored source-law evidence in the endpoint integration while retaining V370/D381/D386; owner decides SHA-NI item3 independently. Privacy target not yet established.
''')
(E/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline',p['revision']+'..HEAD'],text=True)+'\nFinal evidence/report commit follows this snapshot.\n')
print(json.dumps({k:summary[k] for k in ['restored','lean','native','required_remaining']}))
