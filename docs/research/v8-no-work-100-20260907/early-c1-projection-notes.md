# Early C1 projection: proved construction, unfinished concrete endpoint

Research base `f021007879dcd9e2bca795b4758e187fa1c3b302`, 2026-09-09.

The generic optional recovery construction and uniqueness argument are now
kernel checked. The exact V7 log20 fibre-overlap and totalized-C1 base-field
facts have been reused directly. **The specialized Lean application identifying
every qualifying late width29 C1 projection with the early object did not
finish within the bounded local elaboration budget.** It remains an explicitly
unverified draft, not a retained theorem or an achieved acceptance bound.

No Rust, transcript, proof bytes, verifier checks, or production settings changed.

## Mathematical result and intended causal use

[EarlyC1Support.lean](experiments/EarlyC1Support.lean) defines, from a fixed
received word and encoder only, an optional tuple with at least a specified
joint support. It returns `none` precisely when no such tuple exists.
A returned tuple actually has the claimed support. Given an encoder overlap
cap and

```
domain_cardinality + cap < 2 * support_threshold,
```

two qualifying tuples must be identical: their supports intersect in more
than the overlap cap. The proof constructs the intersection; it does not
assume that a later provider succeeded or that a chosen tuple was fixed early.

At the intended C1 parameters,

```
support_threshold = 245609
domain_cardinality = 262144
cap = 256
minimum common support = 2*245609 - 262144 = 229074 fibres.
```

[EarlyC1Arithmetic.lean](experiments/EarlyC1Arithmetic.lean) proves the exact
margin symbolically, without reducing a generated circle domain.
[EarlyC1Projection.lean](experiments/EarlyC1Projection.lean) defines the actual
optional `earlyC1` from the **26 fixed totalized C1 words** and V7's exact
mathematical log20 encoder, and reuses the proved 256-complete-fibre cap.

This definition receives no lambda, chi, C2, gamma, OOD responses, final
polynomial or provider result. It is noncomputable mathematical analysis,
not a decoder implementation or access to a word from a Merkle root alone.

The intended mathematical composition is useful: the dense near-gamma
tuple's own-support conclusion gives a qualifying C1 projection; uniqueness
identifies it with the earlier optional object. Different adaptive C2 words
sharing the same fixed C1 therefore cannot change this supported projection.
Conversely, early `none` would exclude that dense own-support conclusion,
leaving the small-Good branch of the existing dichotomy after its exact-code
instantiation. **This specialized composition was not kernel-closed here**;
no new probability is attached to it.

The first-sixteen-column semantic projection and literal base descent are
also drafted. Base projection preserves supported symbols because C1's
totalized values are embedded M31. Uniqueness would then force the recovered
coefficients into M31 on their own support. This neither requires recovery
on a gamma batch's entire support nor assumes global raw-leaf canonicality.

## Exact retained and draft status

| Artifact / declaration | Evidence and scope |
|---|---|
| `EarlyC1Support.large_support_unique` | Kernel-checked symbolic intersection/overlap argument |
| `early_none_iff`, `some_early_has_support` | Kernel-checked total accounting of the optional construction |
| `early_eq_of_large_support` | Kernel-checked identification for a generic encoder with its stated cap/margin |
| `projection_preserves_support`, `support_restrict` | Kernel-checked generic coordinate projection/restriction |
| `function_agreement` | Kernel-checked vector/pointwise support equality |
| `EarlyC1Arithmetic.c1_margin` | Kernel-checked concrete parameter margin |
| `EarlyC1Projection.exact_fibre_overlap` | Direct V7 mathematical encoder/fibre cap reuse, kernel checked |
| `extracted_totalized_C1_base` | Direct V7 totalization/base-valuedness reuse, kernel checked |
| `EarlyC1Projection.earlyC1` | Checked noncomputable definition, not a practical algorithm |
| Specialized late-width29 identification, early semantic projection/base descent | **Unverified draft**; not claimed in retained Lean |

The concrete draft is preserved in
[EarlyC1Projection.draft.txt](experiments/EarlyC1Projection.draft.txt).
The final unsuccessful minimal instantiation is in
[EarlyC1ProjectionPrefix.draft.txt](experiments/EarlyC1ProjectionPrefix.draft.txt).
Their headers explicitly prohibit treating them as retained Lean results.
No retained `.lean` contains `sorry` or a new axiom.

## V7 reuse and pinned provenance

The reused facts are
`V7C1ConcreteProjectionBinding.exactInitialEncoder_overlap_cap`,
`exactInitialEncoder_commutes`,
`V7C1SubfieldRecovery.projectBase_c1Received`, and the existing V8
`NearGammaFibreBridge.full_fibre_overlap_le_256`.
The last bridge uses the source map `(fibre,slot) ↦ 4*fibre+slot`.

The runner checks all **78 transitive imported Aspis source files** against
the immutable research commit and concurrent main's source bytes, and records
each source/olean SHA256 before and after successful leaves. Mutable K1 work
is not imported. Main advanced from
`782f2d509a7e36efa01d89194c9c813fac84fd3b` to
`099a18ac8dcefafb7c9bc26bd2ae34edb3a1f421`; the imported closure continued
to match the research pin. Cached V7 trace metadata was inspected. This is
pinned cache reuse plus an actual final axiom audit, not a fresh replay of
all V7 source.

| Dependency | Source SHA256 | Olean SHA256 |
|---|---|---|
| V7C1ConcreteProjectionBinding | `78571066d66be07ccfbd526d36be9515be60920cbecc416da467fff44ba1f6e3` | `21dc55087ce72888fcb2c24600f06cf484bfadf4b4f4462109f7807147c9e960` |
| V7C1SubfieldRecovery | `49b135edbb05cc5b28b8c8a4bda764664f015a7e63bfbbee75f3ffcc0687a3ce` | `e512c32d5506c52d1ac33d065e24a2f3321e1d04b43003f1ecf807198621d294` |
| NearGammaFibreBridge | `9e32881435cc4ce2e63ef6ebe4dc04722864f47e205c42d6930c593cd7949631` | `584a64fbbdda15ca3d80c0fe45ebafc5cc1a9bd0788eb21ebc8bfb4f53eb9eef` |

No V7 recovery-error numerator, work-normalised argument, unshifted inactive
claim premise or raw-word/query consistency definition is promoted into a V8
acceptance premise.

## Reproduction and resource outcomes

From the research root, use the runner below with a **new** output log path.
An existing compiled dependency is reused; do not rerun it unchanged.

```sh
EX=docs/research/v8-no-work-100-20260907/experiments
bash "$EX/run_early_c1_projection.sh" generic /tmp/new-early-generic.log
bash "$EX/run_early_c1_projection.sh" arithmetic /tmp/new-early-arithmetic.log
# Only if the previously missing fibre olean is absent:
bash "$EX/run_early_c1_projection.sh" fibre /tmp/new-early-fibre.log
bash "$EX/run_early_c1_projection.sh" leaf /tmp/new-early-concrete.log
```

Apple M3, Lean4.32.0, cached Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. No package/Mathlib/Aeneas/SBF
replay or remote job. Every retained final audit reports only
`propext`, `Classical.choice`, `Quot.sound`.

| Final focused target | Wall | Peak RSS bytes | Swaps | Exit | Axiom declarations |
|---|---:|---:|---:|---:|---:|
| Existing fibre missing-cache export | 39.02s | 5,437,161,472 | 0 | 0 | 3 |
| Generic support, v4 | 0.82s | 1,305,935,872 | 0 | 0 | 7 |
| Independent arithmetic, v1 | 0.82s | 1,370,488,832 | 0 | 0 | 1 |
| Retained concrete leaf, final v2 | 12.25s | 5,637,455,872 | 0 | 0 | 2 |

Final v2 repeats only this small leaf after removing a trailing blank line
reported by the staged diff check. It preserves the same output olean hash.
The before/after imported closure also matches concurrent main at
`94459d0f9700388431c26c1261fbfa6974118af0`; no main files were edited.

The initial full leaf failed after101.24s at8,730,378,240bytes RSS with a
Lean interpreter memory exception despite `-M7000`. No unchanged retry or
larger cap was used. Subsequent changed probes ran with Lake exited before
Lean and a one-second descendant-RSS stop at7GiB; guard-stopped jobs lasted
10.43–22.75s, with sampled peakRSS7.69–7.82GB and0swaps. Their exits are137.
The first failure is exit134. All logs remain under `experiments/early-c1-*.log`.

The simplification sequence was: generic symbolic support lemmas; isolated
concrete cap; removal of unused executable equality requirements; a shared
agreement definition; detached arithmetic; a theorem-header diagnostic;
and an inferred proof-value application. None discharged the final concrete
identification cheaply. We do **not** claim a single confirmed root cause:
predicate/decision-instance mismatches explain the initial rewrite errors,
but neither equality-interface removal nor detached arithmetic alone solved
the last elaboration. Prefix v1/v2 had explicit rewrite errors; v8 reached
the recursion limit. Successful tiny prefixes did not complete the endpoint.
A Bash empty-array preflight did not invoke Lean.

Final retained source/olean hashes:

- Generic: `f8d06ad65042db80ff11c7f162d5cd4a512b9a00b89c3bdbe7dedb414edf4d6d` /
  `47157d9fa29a1d31ec97192a739bdf3b0c802b70c6636c046c840004922b758e`.
- Arithmetic: `a8343405e09566d444890aaceb1fcbaa9d696c4a2d0672c3865a02b184739657` /
  `4b7f1361c0c010c7441cb6ebd4e23787b9fb9ccdd451b9622806e3b765db78bb`.
- Concrete: `c29219e7d1f25f9ef5236fa3d85312a5e33cfbb5a53078ab14e23a4002b9728d` /
  `5f6485d1f9f05ca0ae53b26257dc45a294753d943fa25df6c4bdf792b0dcee14`.

## Remaining obligation

The actual mathematical encoder must still be connected universally to the
Rust FFT. The early optional object is not a resource-bounded extractor.
Acceptance does not yet imply authenticated access to a sufficiently close
C1 word or vanishing selected semantic/copy constraints. The small-Good,
far/no-cover, replay/fuel/provider-none, source/authentication and payment
validation branches remain visible. A totalized field value is not a claim
that its raw leaf encoding is canonical or verifier-accepted.

No new security probability, CU saving or proving-time claim is assigned
to these deterministic facts. The40282-byte allowance, existing restricted
near-binding term, all previous regressions and global open obligations are
unchanged. Full-view ZK and resource-bounded Fiat–Shamir are separate.

The next local formal step is to make the generic support/cardinality
interface opaque enough that its specialized C1 application checks without
enumerating concrete domains. Only then should the early semantic trace be
fed into the selected semantic/copy game at the true C1 fixing boundary.
