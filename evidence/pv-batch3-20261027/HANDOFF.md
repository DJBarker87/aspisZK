# Batch 3 handoff — budget exhausted, target not established

Branch: codex/pv-batch3-20261027, from37e5e133f89f4aa5909a1ca6fc81237d2c977947. Proof/source snapshot:3e053bf03aec623a13dcf2dbd316a460915fdbc1. Final Rust freeze:26ce27b2958eda4328c9531a42145aab1bba7bf0. COMMIT-LOG.txt records the source/proof history through that snapshot; the following receipt commit changes evidence only. No push/merge.

100/100 charged Lean attempts:84 accepted,16 rejected drafts.105 unique IDs consumed, including5 admission-only refusals charged0. Reserved52997/52998/52999 all pass. Kani0. No ELF mismatch, cost stop, fixture disagreement or checked row counterexample. Stop reason: Lean budget exhausted.

## Prover-local groups and gates

All new Rust copy modules are behind the prover feature. Original core/statement bodies remain unchanged. FOREST.md and GROUP2.md/GROUP3.md/GROUP4.md record every caller chain, module gate, source diff and source successor. Source-restored-verification.json confirms738 host input hashes after the temporary evidence-only base build.

| Group | Copies | Initial cumulative worst projection | Evidence |
|---|---|---:|---|
|1|132/133/134/228|+31.6399us|FOREST.md; forest-cost-projection.json|
|2|222/sparse weights/224|+1.687859%|GROUP2.md; group2-cost-projection.json|
|3|226/227 and private terminal caller chain|+1.646089%|GROUP3.md; group3-cost-projection.json|
|4|117/121 and private arithmetic helpers|+1.646513%|GROUP4.md; group4-cost-projection.json|

After the documented source successors, final cumulative projections are transfer+1.6365499625%, withdrawal+1.6420332056%, below2% of14.38s. mask-expanded-projection.json retains earlier measurements for unchanged operations. Per-proof counts and101-pair optimized AB/BA per-call microbenchmarks are retained. No whole-prover timing metric is used. The combined differential/timing gates are the lead's.

All three release pins match after each source stage and successor, including final mask-expanded-elf-01:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

The direct uninstrumented fixed-coin0 fixture gate against37e5e133f8 passes: transfer/withdrawal proof and public bytes identical; both verify in one attempt. Proof hashes2417323b8b8f2b0d1cb1e6e11ee691c312d76465f589dc9222e04ec34747ad3a and3b217e7b8ef188435d5763dd63d2e3f33889965df92b2d69a6338eb9ca4a6d44. See fixture-byte-gate.json and the base-binary source-binding annotations in receipt_corrections.py.

## What is actually proved

Full roots134/117/121 extract with the unchanged pinned tools. PolynomialEmission links30 byte-identical shared declarations and retains8 new declarations, with all normalization recorded. Full Result bounded factorizations, universally quantified over117/121 inputs, are collected in PV_B3_BoundedPacket. These include outer fail/div and all inner errors; they are **not** original/copy equality or row laws.

Complete Result transports on arbitrary raw field carriers cover scalar operations, complex and quartic arithmetic, prepared component/new/mul, and mask power. New-carrier canonicality covers reduction/scalar/complex/quartic operations, prepared helpers, mask power and channel reconstruction under their explicit original hypotheses. Canonical proof ports retain those hypotheses; they do not assert reached native inputs satisfy them.

Ruling(n) inspection plus executable native/emission comparisons pass for134/117/121, including changed outputs and raw limb cases. All mutable restoration functions in these emissions are applied and threaded; see the three *fidelity-comparison.json files. Native comparisons are concrete evidence, not universal original/copy theorems.

132/133/228/222 have pinned-extractor internal failures.224 and227 retain fail-closed preflight refusals;226 has an internal loan failure. External dependency-only117/121 emissions were explicitly rejected as roots and their earlier descriptions corrected. All failures and exact rejected Lean snapshots remain in EXTRACTION.md and receipts.

No requested PV_B3_<name>.opN_source row theorem is claimed. No P premise is removed. Original/copy equality, all row bridges, D234/V403 reached canonicality and the privacy endpoint/deployment/side-channel closure remain P before and after. T is unchanged: exactly entropy_law, entropy_kernel, observation. Target not established.

## Final audits and receipts

| ID | Target | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
|52997|PV_B3_AuditSource|0|1.790|4290888|0|
|52998|PV_B3_AuditCanonical|0|1.586|4291252|0|
|52999|PV_B3_AuditManifest|0|1.559|4297748|0|

All audit source revision3e053bf03aec623a13dcf2dbd316a460915fdbc1. Only propext/Classical.choice/Quot.sound (or no axioms). final-audit-receipts.json has exact targets, source hashes, imported object hashes, cgroup peaks and full #print axioms. receipt-index.json covers every retained run; current-source-coverage.json covers all81 current Lean modules with successful receipts. No shared env-J source/object writes; J is used through the existing run2.py with a private overlay.

One process deviation is retained in GROUP4.md: an early benchmark followed a barrier refusal after107s rather than180s. Both admission checks and caps remained enforced and no scope overlapped; the private wrapper subsequently enforces the full cooldown. No shared admission tool was modified. Another metadata distinction is annotated, not hidden: the base build's invocation workspace revision differs from its explicitly swapped base binary inputs.

Job-private target/sbf-target/charon-target/lean-objects caches were removed after all scopes ended, per local-lean disk hygiene. Source, raw emissions/LLBCs, receipts, binaries, ELF artifacts and durable nonce ledgers remain. No keys/accounts destroyed, no shared paths deleted. cleanup.json records it.

Next concrete deliverable: prove134's original/copy/full-Result row bridge against PV_Op134_* using its checked bounded state machine and sparse endpoint invariants; then resume the remaining extraction and117/121 source/domain bridges with a new budget. The complete requested shared semantic closure is unfinished.
