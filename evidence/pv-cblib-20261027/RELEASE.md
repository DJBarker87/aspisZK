# Library callback resume handoff

Branch `codex/pv-cblib-20261027`; resume baseline `c35956a836e39331f77f632b12eca4320000752d`; source freeze `bdf75de39c3e580415cf79ed2c2d7cd5e7786bf6`. **Target not yet established.** Prior handoff: RELEASE-prior.md.

## Result and premise accounting

Candidate supplied source laws **4 → 5**, adding **V179/op28** by P6. The unchanged four are V177/op25, V180/op29, V185/op34 and V186/op35. OPS.md is the complete 19-op table with route, status, theorem, crate@version, full source SHA and receipts.

Publication remains `R1Z.PV_CBL_CallbackBundle`. All earlier names persist. Additional `StringTypes`/`selectedString` exposes `op28_source`/`op28_source_all` and the four `opN_source_string` laws; `PV_CBL_StringCallbackFamily.supplied` proves all five coexist. These are unconditional data-input laws preserving the complete Aeneas Result. Before: op28 was an arbitrary dictionary field. After: the additional selected dictionary uses the extracted owned String identity. Its native P6 gate covers valid UTF-8 strings of length 2 and arbitrary observation index. This does not assert unbounded or deployed-toolchain equivalence. The old opaque PathBuf selection remains available.

**Canonical endpoint/deployment premises removed: 0.** No endpoint premise or trust item was added or weakened. Native/toolchain/deployed association, E1/E2, RunJoin, L1/L2/L3, client route and coherent repository dependency closure remain retained. The capped trust list T, simulator and observer were unchanged.

## Source and backend results

Pinned sha2@0.10.9 with default/std features on x86_64 compiles its runtime x86 dispatcher: SHA-NI/SSE on the cpufeatures true branch, Rust soft fallback otherwise; asm/force-soft are absent from the recorded candidate fingerprints. SHA-BACKEND.md and sha-dispatch-inventory.json name the exact foreign SHA/SIMD/CPUID symbols and source hashes. The exact nonempty dispatcher LLBC is rejected by Aeneas's escaping-reference preflight. Foreign intrinsic semantics and deployed-artifact/CPU association remain open. No soft backend was silently substituted for the dispatcher.

An owned, byte-checked fallback reference was extracted, with only documented namespace and positive shift-literal type ports. Lean proves its two-round helper and four-round macro model equal conventional scalar SHA transitions; the extracted schedule matches the conventional word recurrence; the feed-forward tail matches wrapping state addition. The complete extracted owned fallback block is proved total on arbitrary typed state/block arrays by a 147-bind symbolic proof. **The complete 64-round output-composition theorem remains open. These support facts discharge no digest row and do not prove SHA-NI compression.** No SHA compression Kani gate ran.

Pure ops 26/30/31 gained split native passes but retain exact loan/destructor/constant-extraction frontiers. Op33's retained reference still needs structured Drop semantics; the mixed singleton Word gate timed out. Op36's retained adapter needs both loan and destructor validation; its length-0–2 rejection gate passes, while the full 1024-element gate timed out. Op217 monomorphization has_errors=true (invalid UInt generics), so Aeneas was not launched. These are tool/proof frontiers, not checked ROW counterexamples. Op32 retains the exact allocator-effect reason in NATIVE-EFFECTS.md; Err was never replaced by Ok.

## Reserved final audits

| ID | target | exit | wall | peak RSS KiB | swap | revision | axioms |
|---|---|---:|---|---:|---:|---|---|
| 43098 | R1Z/PV_CBL_CallbackAudit | 0 | 0:01.75 | 2625332 | 0 | bdf75de39c3e580415cf79ed2c2d7cd5e7786bf6 | standard only |
| 43099 | R1Z/PV_CBL_SelectionAudit | 0 | 0:08.00 | 2625976 | 0 | bdf75de39c3e580415cf79ed2c2d7cd5e7786bf6 | standard only |
| 43100 | R1Z/PV_CBL_FinalManifest | 0 | 0:02.94 | 2631540 | 0 | bdf75de39c3e580415cf79ed2c2d7cd5e7786bf6 | standard only |

One final frozen own-module manifest: 151 imports, 506 explicit axioms queries; 152 current-source own modules accepted including the manifest. Every final axiom set is a subset of propext, Classical.choice, Quot.sound. This is an own-module import/axioms manifest, not a clean repository-wide or deployed privacy replay.

## Budget, receipts and custody

Lean **100/100**: 86 exit-zero runs, 84 standard-axiom accepted runs. Diagnostic 43034/43035 introduced native certificate axioms and are explicitly rejected; kernel replacements 43037/43038 pass. All failed/recovery artifacts are rejected. Kani **8/8**: six bounded passes, two 180-second timeouts, no checked ROW counterexample. Env-J IDs 43000–43100 were used once; 43014 was an uncharged admission refusal; next unused ID 43101. The last three charged Lean attempts were reserved audits.

RESUME-RECEIPTS.json and each numbered JSON contain exact target, exit, wall, peak RSS, swap, source revision, source/dependency hashes and full printed axioms. LEAN-RECEIPTS.md and KANI-SUMMARY.md index them. Native timeout RSS is the GNU-time wrapper measurement, not aggregate killed-descendant solver RSS; that unavailable aggregate is not invented. Both timed-out scopes were confirmed gone. All scopes used 6G high / 8G max / swap 0, with standing task caps; no cap, depth or heartbeat limit was increased.

The Rust production prefix is byte-identical to the candidate base; production-file changes are only cfg(kani) harness modules. ProverRw sources and other worktrees were read-only. No production ELF change or new ELF association is claimed. 152 accepted own objects are retained in the pinned host lean-objects cache. This job's kani-target/charon-target scratch was removed; sources and receipts remain. No shared /tmp sweep or shared source replacement was performed. No push or merge.

## Next concrete deliverable

pv-wire/recount can consume the fifth stable bundle law with its explicit P6 bound and association caveats. To close additional rows, validate the exact loan/destructor paths (plus String.new constant conversion), prove the complete fallback block value composition, and extract/model the shipped x86 dispatcher and SHA-NI semantics without stubs. Keep native allocator, deployment, side-channel and client obligations named until their actual joins are proved. Work stopped on exhaustion of both authorized budgets.

## Resume commits

```text
bdf75de39c Freeze five-law callback publication and fallback support manifest
0bc9effba5 Prove extracted fallback helper laws and symbolic block totality
70613ba8a9 Record remaining allocation frontiers and pinned x86 SHA dispatcher
54fa76837c Publish owned String path-view law and split native library gates
```

The final receipts/report commit follows this source freeze. Prior budget/results remain in TALLY-prior.json and the *-prior.md artifacts.
