"""Write the exhausted resume budget handoff and exact receipt tables."""
from pathlib import Path
import json,subprocess,re
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';t=json.loads((out/'TALLY.json').read_text());assert len(t['lean_charged'])==100 and len(t['kani_charged'])==8
lean=[json.loads((out/f'{a}.json').read_text()) for a in t['lean_charged']];accept=json.loads((out/'RESUME-ACCEPTANCE.json').read_text());manifest=json.loads((out/'manifest-source-pins.json').read_text());native=[(n,json.loads((out/n/'collected-receipt.json').read_text())) for n in t['kani_charged']]
for filename in ['LEAN-RECEIPTS.md','KANI-SUMMARY.md']:
 p=out/filename;prior=out/(p.stem+'-prior.md')
 if not prior.exists():prior.write_bytes(p.read_bytes())
p=out/'RELEASE.md'
p.write_text('''# Library callback resume handoff

Branch `codex/pv-cblib-20261027`; resume baseline `c35956a836e39331f77f632b12eca4320000752d`; source freeze `bdf75de39c3e580415cf79ed2c2d7cd5e7786bf6`. **Target not yet established.** Prior handoff: RELEASE-prior.md.

## Result and premise accounting

Candidate supplied source laws **4 → 5**, adding **V179/op28** by P6. The unchanged four are V177/op25, V180/op29, V185/op34 and V186/op35. OPS.md is the complete 19-op table with route, status, theorem, crate@version, full source SHA and receipts.

Publication remains `R1Z.PV_CBL_CallbackBundle`. All earlier names persist. Additional `StringTypes`/`selectedString` exposes `op28_source`/`op28_source_all` and the four `opN_source_string` laws; `PV_CBL_StringCallbackFamily.supplied` proves all five coexist. These are unconditional data-input laws preserving the complete Aeneas Result. Before: op28 was an arbitrary dictionary field. After: the additional selected dictionary uses the extracted owned String identity. Its native P6 gate covers valid UTF-8 strings of length 2 and arbitrary observation index. This does not assert unbounded or deployed-toolchain equivalence. The old opaque PathBuf selection remains available.

**Canonical endpoint/deployment premises removed: 0.** No endpoint premise or trust item was added or weakened. Native/toolchain/deployed association, E1/E2, RunJoin, L1/L2/L3, client route and coherent repository dependency closure remain retained. The capped trust list T, simulator and observer were unchanged.

## Source and backend results

Pinned sha2@0.10.9 with default/std features on x86_64 compiles its runtime x86 dispatcher: SHA-NI/SSE on the cpufeatures true branch, Rust soft fallback otherwise; asm/force-soft are absent from the recorded candidate fingerprints. SHA-BACKEND.md and sha-dispatch-inventory.json name the exact foreign SHA/SIMD/CPUID symbols and source hashes. The exact nonempty dispatcher LLBC is rejected by Aeneas's escaping-reference preflight. Foreign intrinsic semantics and deployed-artifact/CPU association remain open. No soft backend was silently substituted for the dispatcher.

An owned, byte-checked fallback reference was extracted, with only documented namespace and positive shift-literal type ports. Lean proves its two-round helper and four-round macro model equal conventional scalar SHA transitions; the extracted schedule matches the conventional word recurrence; the feed-forward tail matches wrapping state addition. The complete extracted owned fallback block is proved total on arbitrary typed state/block arrays by a 147-bind symbolic proof. **The complete 64-round output-composition theorem remains open. These support facts discharge no digest row and do not prove SHA-NI compression.** No SHA compression Kani gate ran.

Pure ops 26/30/31 gained split native passes but retain exact loan/destructor/constant-extraction frontiers. Op33's retained reference still needs structured Drop semantics; the mixed singleton Word gate timed out. Op36's retained adapter needs both loan and destructor validation; its length-0–2 rejection gate passes, while the full 1024-element gate timed out. Op217 monomorphization has_errors=true (invalid UInt generics), so Aeneas was not launched. These are tool/proof frontiers, not checked ROW counterexamples. Op32 retains the exact allocator-effect reason in NATIVE-EFFECTS.md; Err was never replaced by Ok.
''')
with p.open('a') as f:
 f.write('\n## Reserved final audits\n\n| ID | target | exit | wall | peak RSS KiB | swap | revision | axioms |\n|---|---|---:|---|---:|---:|---|---|\n')
 for r in lean[-3:]:
  f.write(f"| {r['attempt']} | {r['module']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swap']} | {r['source_revision']} | standard only |\n")
 f.write(f"\nOne final frozen own-module manifest: {manifest['imports']} imports, {manifest['declarations']} explicit axioms queries; 152 current-source own modules accepted including the manifest. Every final axiom set is a subset of propext, Classical.choice, Quot.sound. This is an own-module import/axioms manifest, not a clean repository-wide or deployed privacy replay.\n")
 f.write(f"\n## Budget, receipts and custody\n\nLean **100/100**: {sum(r['exit']==0 for r in lean)} exit-zero runs, {sum(r['accepted'] for r in accept)} standard-axiom accepted runs. Diagnostic 43034/43035 introduced native certificate axioms and are explicitly rejected; kernel replacements 43037/43038 pass. All failed/recovery artifacts are rejected. Kani **8/8**: six bounded passes, two 180-second timeouts, no checked ROW counterexample. Env-J IDs 43000–43100 were used once; 43014 was an uncharged admission refusal; next unused ID 43101. The last three charged Lean attempts were reserved audits.\n")
 f.write('\nRESUME-RECEIPTS.json and each numbered JSON contain exact target, exit, wall, peak RSS, swap, source revision, source/dependency hashes and full printed axioms. LEAN-RECEIPTS.md and KANI-SUMMARY.md index them. Native timeout RSS is the GNU-time wrapper measurement, not aggregate killed-descendant solver RSS; that unavailable aggregate is not invented. Both timed-out scopes were confirmed gone. All scopes used 6G high / 8G max / swap 0, with standing task caps; no cap, depth or heartbeat limit was increased.\n')
 f.write('\nThe Rust production prefix is byte-identical to the candidate base; production-file changes are only cfg(kani) harness modules. ProverRw sources and other worktrees were read-only. No production ELF change or new ELF association is claimed. 152 accepted own objects are retained in the pinned host lean-objects cache. This job\'s kani-target/charon-target scratch was removed; sources and receipts remain. No shared /tmp sweep or shared source replacement was performed. No push or merge.\n')
 f.write('\n## Next concrete deliverable\n\npv-wire/recount can consume the fifth stable bundle law with its explicit P6 bound and association caveats. To close additional rows, validate the exact loan/destructor paths (plus String.new constant conversion), prove the complete fallback block value composition, and extract/model the shipped x86 dispatcher and SHA-NI semantics without stubs. Keep native allocator, deployment, side-channel and client obligations named until their actual joins are proved. Work stopped on exhaustion of both authorized budgets.\n')
 f.write('\n## Resume commits\n\n```text\n'+subprocess.check_output(['git','log','--oneline','c35956a836..HEAD'],text=True).strip()+'\n```\n\nThe final receipts/report commit follows this source freeze. Prior budget/results remain in TALLY-prior.json and the *-prior.md artifacts.\n')
lines=['# Resume Lean receipt inventory','','Every numbered JSON preserves the exact target, source/dependency hashes, metrics and full axioms. Exit zero alone is not acceptance; 43034/43035 are rejected native-certificate diagnostics.','','| ID | target | exit | wall | peak RSS KiB | swap | revision | receipt |','|---|---|---:|---|---:|---:|---|---|']
for r in lean:lines.append(f"| {r['attempt']} | {r['module']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swap']} | {r['source_revision']} | [{r['attempt']}.json]({r['attempt']}.json) |")
(out/'LEAN-RECEIPTS.md').write_text('\n'.join(lines)+'\n')
lines=['# Resume bounded Kani gates','','No stubs; small-width control/indexing only. No SHA compression gate. All exact targets, source snapshots, revisions and cap records are in each collected-receipt.json.','','| run | exit | wall | reported peak KiB | swap | verdict |','|---|---:|---|---:|---:|---|']
for n,r in native:
 verdict='PASS (bounded harness only)' if str(r['exit'])=='0' else 'TIMEOUT; no verdict; RSS excludes killed descendants' if str(r['exit'])=='124' else 'REJECTED; no equivalence verdict'
 lines.append(f"| {n} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swap']} | {verdict} |")
lines+=['','Charged 8/8. Six passes, two 180-second timeouts, no checked ROW counterexample. Timeout scopes checked absent; native/compiler/deployed associations remain explicit. #print axioms: N/A native runs. Prior ten-run budget is preserved in KANI-SUMMARY-prior.md.']
(out/'KANI-SUMMARY.md').write_text('\n'.join(lines)+'\n');print('final handoff and 100/8 receipt tables written')
