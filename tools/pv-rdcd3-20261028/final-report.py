"""Final receipt index and scoped report, only after all required gates pass."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028'
for n in ['lean-60697','lean-60698','lean-60699','final-coherence']:
 assert json.load(open(E/n/'receipt.json'))['exit']==0,n
runs=[dict(receipt=str(p.relative_to(E)),**json.loads(p.read_text())) for p in sorted(E.glob('*/receipt.json'))]
lean=[x for x in runs if x.get('module')];native=[x for x in runs if not x.get('module')]
assert len(lean)==100 and len(native)==9 and all(x['swap']=='0' for x in runs)
assert {x['attempt'] for x in lean}==set(range(60600,60700))
for x in runs:assert all(k in x for k in ['target','exit','wall','peak_rss_kib','swap','source_revision','axioms'])
(E/'RUNS.json').write_text(json.dumps(runs,indent=2)+'\n')
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
(E/'COMMITS.txt').write_text('Commit snapshot through '+revision+' (report-only commit follows).\nReproduce current full log: git log --oneline 96f705ea1a..HEAD\n\n'+subprocess.check_output(['git','log','--oneline','96f705ea1a..HEAD'],text=True))
history=E/'HISTORY.md'
if not history.exists():history.write_text('# Superseded chronological WIP / capacity-resume receipts\n\nThe final REPORT.md is authoritative.\n\n'+(E/'REPORT.md').read_text())
rows={p.stem:json.loads(p.read_text()) for p in (E/'rows').glob('V*.json')}
assert sorted(k for k,v in rows.items() if v['status']=='RESTORED')==['V217','V260','V265']
lines=['# PV_RDCD3 final deployed-source disposition','',
'**3 RESTORED at stated source/Result boundaries; 6 SUSPENDED. Privacy target not established.**','',
'Branch `codex/pv-rdcd3-20261028`, base `96f705ea1a`; exact assigned worktree retained. [Commit snapshot](COMMITS.txt), [all run receipts](RUNS.json), [machine-readable status](STATUS.json), [capacity-resume history](HISTORY.md). No push, merge, crates/programs, dictionary, simulator, observer or T changes. No wallet/account keys were created or touched.','',
'| Row | Status/class | Exact result or retained blocker |','|---|---|---|']
short={
'V260':'Both original253 and selected251 complete Result APIs; concrete range/fold/index/word/control and table binding.',
'V265':'Static circle control and exact M31 inverse backend, including zero assertion. Pointer-form Kani remains quarantined.',
'V217':'Complete selected-mask source/owned Result equality; exact fills, reverse statistics/Horner, field/backend and library source bindings.',
'V220':'Complete radix-four evaluator/qm31_sum_products3 lazy-accumulation source/library transport remains open;20 conservative records. Pin/projection tools are not original checkers.',
'V237':'Concrete GenericArray builder/default-byte/initialization and drop cone remains open;4 conservative panic/callback records.',
'V236':'Concrete BlockBuffer::digest_blocks buffer/slice-copy/index source law remains open. The compression callback alone is parametric; the old two-body graph is incomplete.',
'V197':'Pinned Aeneas loan-validation rejection remains. Owned SliceRange/TryArray/endian/ordered-parser drafts are uncompiled and give no credit.',
'V233':'Complete1.94.1 raw-parts/offset/transmute/GenericArray byte-block representation transport remains open;61 records.',
'V201':'Complete concretely instantiated ChunksExact/Zip/array-iterator/index source/library transport remains open;145 records.'}
for v in ['V260','V265','V217','V220','V237','V236','V197','V233','V201']:
 j=rows[v];lines.append(f"| [{v}](rows/{v}.md) | {j['status']} / {j['class']} | {short[v]} |")
lines += ['',
'The three restored rows use evidence class **structural (K-1 substitute)**. This is **reclassification within existing Aeneas/Rust/compiler tool trust, never premise removal**. V260/V217 original complete checkers were not recovered or relabelled: their owned structural route is under k-prime/own-1. Exact before/after statements, unchanged input quantifiers/Result carrier, and all retained obligations are in the row JSON/MD records. The kernel checks the stated Lean laws; no Rust machine-code or physical-observer theorem is asserted.','',
'Native source association uses pinned1.94.1 library/application bodies, deployed `r1p-check`/`ct-host-prover` feature selection and release debug/overflow settings. [Per-crate configuration](deployed-client-features.json) and [unchanged finite-fixture pins](v217-native-reuse.json) are retained. No new extractor or Kani run occurred. Any inherited extraction/Rust agreement retains existing tool trust and the V370/D381/D386 compiler-cohort boundary. h5-double-prime is unused; b3p6-1 token identity/extractor reproduction is not claimed. Common Lean field-body identity is only [supporting model evidence](field-model-association-result.json).','',
'V217 source checks cover six application bodies,26 field bodies and six additional reverse-library bodies, plus existing range/index/write/widening/wrapping bindings. Stores preserve all returned arrays. Every conservative match is dispositioned by concrete receiver and source/Result scope; counts alone are not a complete monomorphization certificate. Mutation controls are syntactic fail-closed checks, not compiled fidelity controls. Native arithmetic/range/constant fixtures remain finite validation and were reused at unchanged pins; no universal compiled-artifact inference is made.','',
'## AGENTS.md section 6 evidence','',
'All100/100 Lean attempts are used:86 pass,14 fail.9/100 capped native scopes:8 pass,1 fail.0 Kani. Refusals are uncharged. Every exact command target, exit, wall time, peak RSS, swap, source revision, source/dependency fingerprint and full axiom output is in [RUNS.json](RUNS.json) and its linked original receipt/log. Declaration-only and native checks have no new theorem axiom claim.','',
'| Final target | Exit | Wall | Peak RSS KiB | Swap | Exact source revision / axioms |','|---|---:|---|---:|---:|---|']
for name in ['lean-60697','lean-60698','lean-60699','final-coherence']:
 j=json.load(open(E/name/'receipt.json'));axioms='N/A, source/object check' if name=='final-coherence' else 'subset of propext, Classical.choice, Quot.sound'
 lines.append(f"| [{name}]({name}/receipt.json) | {j['exit']} | {j['wall']} | {j['peak_rss_kib']} | {j['swap']} | `{j['source_revision']}`; {axioms} |")
lines += ['',
'60697 audits491 declarations from83 successful focused source modules;60698 replays every restored row’s complete statement (including both V260 APIs);60699 is the single final frozen manifest of this job’s accepted changed closure. All pass with only standard axioms. The five [uncompiled drafts](UNCOMPILED-DRAFTS.json) are excluded and uncredited. Successful fill/reverse-statistics totality helpers are additional model facts; the optional whole-function totality bridge is not claimed.','',
'[Final independent coherence](final-coherence-result.json) checks86 successful private modules, every original launch dependency snapshot and all5673 h4 external object hashes. V217’s own subclosure has41 project bindings. All actual scopes use6G high/8G max/swap0/Tasks64; Lean -M7000. No cap was raised. [Cooldown audit](cooldown-audit.json):109 actual launches,3 host refusals, zero timing violations; minimum gap '+str(json.load(open(E/'cooldown-audit.json'))['minimum_gap_seconds'])+' seconds. One local pre-submission cooldown refusal launched nothing. Prior pv-rdcd violations remain separately documented; void objects were not re-used for credit.','',
'Failed elaborations and the failed native negative-control generator remain visible and uncredited. No memory-killed job was rerun unchanged. No unchanged full arithmetic/runtime regression was repeated. The final manifest is this job’s changed accepted proof cohort, not a replay or proof of the full privacy endpoint.','',
'## Retained obligations and handoff','',
'Endpoint premises removed0, added0, changed0. E1/E2, real native RunJoin/carrier/world (V165–V167), client proof-account route, L1/L2/L3 and binary/physical-observer obligations remain. Panic diagnostics/runtime effects outside the source-value projection remain. T is exactly entropy_law, entropy_kernel, observation. V265 historical circle/injected-inverse function-pointer Kani qualifications remain **QUARANTINED**; no such PASS is consumed or unquarantined.','',
'Stopping basis: Lean budget exhausted after required audit/replay. Native scopes are an upper bound; unchanged checks were not repeated to consume them. Six rows retain their concrete blockers above. **Next deliverable: bind the complete deployed V220 radix-four evaluator and qm31_sum_products3 lazy-accumulation/helper library cone, then prove its unchanged complete Result law.**','',
'[Cleanup](cleanup-result.json) removed only identified own compiler caches and optimized test executables after final coherence. Sources, emitted/model text, fingerprints and receipts remain. The recorded object hashes are historical final measurements; those own compiled caches are no longer available for h6 reuse. No keys or other job/shared targets were removed.']
(E/'REPORT.md').write_text('\n'.join(lines)+'\n')
(E/'HANDOFF.md').write_text('''# Budget-exhausted handoff

100/100 Lean attempts used: IDs60600–60699. No assigned Lean ID remains.
9 capped native scopes,0 Kani. All final audit/replay/coherence targets pass.
V260/V265/V217 RESTORED/B at source-value/Result scope; six rows SUSPENDED.
Endpoint premises removed/added/changed0. Privacy target not established.
Read REPORT.md, STATUS.json, rows/*.json and RUNS.json for exact scope/evidence.
Five uncompiled drafts are explicitly excluded in UNCOMPILED-DRAFTS.json.
Own compiled caches were removed after final verification under local cleanup
rules; retained sources/receipts/hashes are not surviving objects. No keys touched.
Next: V220 full radix-four/qm31_sum_products3 source/library Result transport.
''')
print('Final report and109-run receipt index written; no further compile')
