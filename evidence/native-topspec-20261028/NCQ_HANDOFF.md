# NCQ handoff

Branch: `codex/cx-native-topspec-20261028`. No push. Stage 1 commit: `d66473cca7` (contract/design audit). Stage 2 commit contains this handoff, new Lean module and focused receipts.

## Established

`NCQ_TOPSPEC.md` audits the three exact full-domain fields of `S2W_DigestExtraction.AeneasExtraction`, their nested Result semantics, actual owned entries versus AccountInfo wrappers, required Rust reference contracts, semantic link classifications, and a narrower trust-row draft explicitly NOT adopted. It preserves the exact replayed installed SDK and distinguishes output correspondence from native attempted-call history. Input/source pins are in `NCQ_INPUTS.json`; fresh prints of the RPx closure's definitions are in `NCQ_L001/stdout.log`.

`lean/NCQ_TopSpec.lean` checks:

- `fields_iff`: exact conjunction of all three unrestricted fields.
- `assemble`: reference-to-model equalities plus explicit semantic-link hypotheses imply extraction.
- `factor_iff`: existential reference factoring is equivalent to the existing extraction premise, so repackaging alone discharges nothing.
- `digest_source_iff`: the source-wrapper requirement is equivalent to equality with hashv, including non-returning cases.
- `model_instance`: model-instantiated stage functions satisfy stage fields by definition, retaining the digest premise; no association to Rust follows.

These are model/interface theorems and a reused digest source-helper theorem, NOT a concrete source-to-model refinement, composed security theorem, or connection to frozen release artifacts.

## Validation

1/40 Lean attempts, 0/0 Kani. `NCQ_L001`: one focused `lake env lean -j1 -M7000 -DElab.async=false` compile, exit 0, 2.240618 seconds, peak RSS 4,390,744 KiB, swaps 0. Raw cgroup memory peak: 495,357,952 bytes (reported separately from time's RSS metric). Scope verified MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Admission allowed=true AND exit 0; no retries. All five new theorems print exactly `[propext, Classical.choice, Quot.sound]`. Full command, source revision/dirty flag/hash, direct imported object hashes and toolchain hash are in receipt and `NCQ_ATTEMPTS.jsonl`.

Reused the RPx dependency closure in its inherited search order, with the private cache seeded by `cp -a` from the read-only leaf cache. No dependencies rebuilt, no existing proof edited, no package/frozen-manifest replay, no runtime/adversarial/reproducible-build suite: this is a focused boundary audit, not a release replay. Own cache retained at `/home/dombarker/project-offloads/codex-cx-topspec-cache-20261028`. No keys created or removed.

## Retained obligations and next deliverable

No native extraction premise was discharged, removed or weakened; no cryptographic assumption added. Rust contract composition can replace unchecked algorithmic assertions with evidence only after actual full-domain top contracts, controls, coverage/abnormal-outcome arguments and extracted-reference-to-exact-SDK Lean proofs exist. The semantic association of Kani's Rust, Aeneas's reference extraction and arbitrary Lean native parameters remains meta-level tool/representation trust. Existing P6/D188 scope coverage is an OWNER decision; absent that coverage it is a gap needing a row, not an adopted assumption. Draft exact wording is in NCQ_TOPSPEC.md.

The next concrete deliverable is a fully pinned top-entry/reference certificate and model equality, with all rejected inputs/errors, external effects, domain and function-pointer quarantine conditions accounted for. The known error-to-panic discrepancy must be proved irrelevant at the exact boundary or the exact equality cannot follow; generic rejection is a different relation. D188-P2 association, P1/RuntimeSyscall, wrapper/std/allocator/field boundaries, native trace transport and P7/S10 artifact association remain separate. Target not yet established.
