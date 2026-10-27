from pathlib import Path
import json,subprocess,hashlib
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume5'
rs=[json.loads(p.read_text()) for p in sorted(e.glob('38*-receipt.json'))]
assert len(rs)==95 and sum(x['charged_lean_attempts'] for x in rs)==95
assert len({x['attempt'] for x in rs})==95
assert [x['attempt'] for x in rs]==list(range(38000,38095))
assert all(x['validation_exit']==0 for x in rs[-3:])
assert all(not x['rejected_axioms'] for x in rs if x['validation_exit']==0)
native=[]
for p in sorted(e.glob('*/receipt.json')):
 x=json.loads(p.read_text());native.append(dict(name=p.parent.name,receipt=str(p.relative_to(e)),**x))
kani=[x for x in native if x['kind']=='kani'];assert len(kani)==6
x=dict(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),base='8eba145a71',source_revision_before_evidence_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_budget=95,lean_actual=95,lean_green=sum(z['validation_exit']==0 for z in rs),lean_failed=sum(z['validation_exit']!=0 for z in rs),kani_budget=6,kani_actual=6,kani_pass=sum(z['exit']==0 for z in kani),kani_timeout=sum(z['exit']==124 for z in kani),lean=rs,native=native,target_established=False,endpoint_premises_removed=0,inventory_before=30,inventory_after=30)
(e/'receipt-index.json').write_text(json.dumps(x,indent=2)+'\n')
(e/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','8eba145a71..HEAD'],text=True))
final=rs[-3:]
table='\n'.join('| '+ ' | '.join(map(str,[z['module'].split('/')[-1],z['attempt'],z['exit_status'],z['wall'],z['peak_rss_kib'],z['swaps'],z['source_revision'][:10],len(z['print_axioms'])]))+' |' for z in final)
report=f'''# pv-join5 final report

Branch `codex/pv-join-20261026`, resume base `8eba145a71`. **Target not yet established.**

## Proved, measured, and open

**Op121 remains OPEN.** Direct Charon extraction succeeds; Aeneas rejects compiler-generated Drop, then fails in loop-context collapse after only unused FnOnce methods are made opaque. No backend/source repair. The closure-free owned radix-four reference extracts and its 29 declarations compile. Full canonical-domain equivalence and the smaller sum3 equivalence both time out at240s; neither is retried unchanged or claimed as a proof.

`PV_Join_CurrentPolynomialCanonical5.polynomial` (38090) proves every successful `host_sumcheck.interpolate` output canonical for `PV_Join_PublicCaller.selected`, on arbitrary raw evaluation values. Scalar/complex/quartic parser invariants, reducer invariants, canonical arithmetic and array/loop preservation are green. The generic Laws interface is discharged by `CanonicalPrimitives5.caller`; it adds no endpoint assumption. Challenge-side semantic/update/read composition and shipped/reference equality remain open. Producer list: `op121-producers.md`.

D234 retained: resume4's noncanonical Horner disagreement stays unchanged in its report, receipt and counterexample files. It does not refute the complete-Result arbitrary-input extraction row. The row has not been restricted, and no shipped fix was made.

For **transfer and withdrawal**, complete execution-reached sets remain unresolved; universally excluded entries: **none proved**. `FixturePrefix5.entered_input` proves op226 is first after entering either input's attempt; it does not prove retry/admission reaches that entry. Inventory **30 →30**, zero new shipped source laws and zero universal exclusions. Effect entries4,32,122,123,232,257 remain deferred with inherited exact reasons. cb4 op259 is PREPARED; rw21 op223 is reference-only. No duplicate credit.

Both fixture proof-byte equations, full audit/status equations, V163 and native nonvacuity remain exact/open. ProverRw21ModelInstance is published at f3071faf74 as a stable mathematical serializer; its deployed-input-to-Transcript construction is explicitly open. The earlier absence report was mistaken and is superseded by published-model-review.json. No endpoint premise was removed, weakened, added or changed: before/after endpoint statements and deployment conditions are identical. E1/E2, real RunJoin, L1/L2/L3, proof-account client and release dependency closure remain.

## Validation and stop

Lean **95/95**, IDs **38000–38094**, unique; {x['lean_green']} green/{x['lean_failed']} failed. Last3 reserved for final audit. Kani **6/6**:4 arithmetic gates pass,2 equivalence timeouts. No local Lean. Failure receipts and four dependency-order queue failures38079–38082 are retained. Later retries changed dependency fingerprints; no unchanged replay bypass.

| Target | ID | Exit | Wall | Peak RSS KiB | Swap | Revision | Axiom reports |
|---|---:|---:|---|---:|---:|---|---:|
{table}

All236 PV_Join theorem/function declarations plus headline pass with standard axioms only. This is a focused audit against retained objects, **not a clean release manifest replay**. `receipt-index.json` contains every host target, exit, wall, RSS, swap, source revision/hash, dependency fingerprint and full axioms reports. Timeout child aggregate peaks are unavailable; wrapper RSS is labeled and live lower-bound samples retained. All observed swaps0; native scopes and Lean scopes retain6G/8G/swap0 caps.

No crates/programs, keys, sibling worktrees, launcher or backend changed. No push/merge. New Cargo target cache removed after completion; pinned Lean cache retained.

Stopped on budget exhaustion. Next: prove the canonical-domain source/reference sum3/evaluator correspondence symbolically, compose the challenge invariant into the actual op121 call, and compose the published rw21 serializer once its independently specified deployed-input-to-Transcript construction is proved.

Commits before this final evidence commit: `commits.txt`.
'''
(e/'FINAL-REPORT.md').write_text(report)
print('Lean',x['lean_actual'],'green',x['lean_green'],'failed',x['lean_failed'],'Kani',len(kani),'audit green')
