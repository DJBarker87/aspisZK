# Secure-circle parameter recovery and successful-byte injectivity

Checked: `experiments/SecureCircleParameterInverse.lean`, NUC v8, exit 0.
All 16 printed theorem audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx`, new axiom, production change, or field enumeration.

## Endpoint

For a field of characteristic different from two, the generic proof derives

`((t+t)/(1+t²)) / (1+(1-t²)/(1+t²)) = t`

when `1+t² ≠ 0`, and derives coordinate-pair injectivity. The concrete QM31
nonzero-two guard is discharged by the pinned V7 characteristic lemma, not by
enumerating the field or assuming a generic basis property.

`recoverParameter` decodes the **actual returned x and y bytes** and computes
`y/(1+x)`. `recover_success` proves that this returns `some t` from only
`exactSecureCirclePointFromDecoded t = some point`. It derives the successful
inverse branch and literal output encodings from that run. In particular, the
endpoint does not ask its caller for the coordinate formulas, nonzero
denominator, canonical input, or separately successful inverse.

`successful_map_recovers` goes through the actual byte decoder and produces its
decoded value. Finally, for any two successful byte-level runs,

`successful_points_eq_iff` proves `first = second ↔ leftBytes = rightBytes`,
and `successful_points_ne_iff` proves the corresponding inequality equivalence.
These implications include arbitrary input bytes: malformed/noncanonical bytes
are excluded by the successful-run premise itself, not by an honest-encoding
assumption.

## Exact reuse and source interface

Working source parent: `ce36c58168987142d3f07e5d8cba00fb7b1dd05b`.
Borrowed V7 pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The three borrowed files below were checked unchanged against that pin with
`git -C /Users/dominic/ZK diff --exit-code <pin> -- <paths>`.

| Source | Consumption |
| --- | --- |
| `AspisFormal/K1/V7Tag73SecureCircleMap.lean` | Actual source-shaped nested `try_inv`/subfield checks; literal canonical x/y encodings; exact optimized-square/Karatsuba identities; successful inverse correctness; actual byte parameter map. |
| `AspisFormal/K1/V7Tag73SemanticTranscriptBridge.lean:437–505` | Four codec right-inverse/injectivity proof bodies reused in the new `Codec` namespace and rechecked, retaining their actual finite four-byte/four-limb argument. |
| `AspisFormal/K1/V7ExactCorrelatedAgreementFactors.lean:465` | `qm31Exact_natCast_ne_zero_of_pos_of_lt_characteristic`, instantiated at two. |
| `crates/aspis-core/src/circle.rs:34–65` | Rust computes square, inverse of `1+square`, x and y, then applies the OOD subfield exclusion; it agrees with the existing V7 mathematical model's check order. |
| `experiments/inactive_row_binding.rs:58–60` | The selected distinct-point comparison can consume the successful inequality equivalence; this leaf does not formalize its whole retry loop. |

The full V7 SemanticTranscriptBridge artifact was **not imported**. Metadata
inspection found 31 additional modules and 12 existing-boundary olean variants;
mixing those caches was avoided. Only the four necessary V7 proof bodies were
ported, using already-pinned SecureCircleMap/Factors imports. This is a new
kernel check of reused proof source, not a claim that the large V7 transcript
closure was replayed.

Source SHA-256:

- SecureCircleMap: `6b3497ca6a87bbb87f71653a25a419745b65123eec769156ff33ba6cd2669070`.
- SemanticTranscriptBridge: `91ada7d79b858d045eacb57a4b8a34b5e01594800f8829fea0888b4820c3f189`.
- CorrelatedAgreementFactors: `112e16cd05454f76e65958025ed01fd45e07dd2cf0632ee5eb53e2170b4ad8f3`.
- Rust circle source: `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c`.

## Focused evidence and failed diagnostics

Every attempt has retained `experiments/secure-circle-parameter-inverse-nuc-vN`
`-source.txt`, `-manifest.json`, and `.log`. Failed logs are diagnostics, not
successful theorem/axiom evidence. Their downstream `sorryAx` entries disappear
in the complete green v8 audit.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Result/change |
| --- | ---: | ---: | ---: | --- |
| v1 | 1 | 3.28 | 6807460 | Seven generic/codec audits checked; namespace-dot parsing, rewritten decoder equality, and concrete arithmetic conversion failed. |
| v2 | 1 | 3.15 | 6807812 | First two local issues closed; compound QM31 conversion still exceeded recursion depth 200. |
| v3 | 1 | 3.22 | 6808112 | Generic multiplication-form normalization checked; direct concrete application still failed. |
| v4 | 1 | 3.55 | 6814520 | Explicit-type diagnostic isolated native quadratic Div/Sub versus field-projected instances. |
| v5 | 1 | 4.10 | 6807784 | Abstract one-layer wrapper checked, but did not settle the concrete nested seam. |
| v6 | 1 | 5.30 | 6807964 | Two-layer wrapper did not settle the seam; wrapper experiments subsequently removed. |
| v7 | 1 | 3.28 | 6808280 | Actual native subtraction proved coordinatewise and division rewritten to multiplication/inverse; only compound equality matching remained. |
| v8 | 0 | 3.43 | 6842872 | Bounded congruence conversion (`using 2`) closed the final equality; all 16 audits standard-only. |

All attempts used zero swaps and unchanged depth/heap/cgroup caps. No unchanged
source retry or cap escalation occurred. The final source retains the explicit
coordinate subtraction lemma and generic subtraction-free inverse; the failed
wrapper experiments and expanded diagnostic printer are absent.

The serialized command was sent through Tailscale numeric IP `100.108.41.90`
with `BatchMode`, `ConnectTimeout=10`, `StrictHostKeyChecking=yes`, and
`HostKeyAlias=nuc.local` solely for the verified host key:

```text
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh /home/dombarker/project-offloads/aspis-higher-y.fMoMeX SecureCircleParameterInverse secure-circle-parameter-inverse-nuc-v8
```

The log records the exact Lean 4.32.0 command, `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, and CPU quota 200%. Scope creation parent
remains `289d7356c78a4cd493fe61a54f9548f2a0c11298`; it is distinct from this
leaf's working parent. Preflight had no other user build scope and 43 GiB
available. Postflight: 857 provenance entries passed, unchanged. Native package
artifacts remain a pinned-revision cache boundary, not a package replay.

Final hashes:

- Source and v8 snapshot: `71630c1927e6564572d3b29899e7b1cf6f1feb5a1d2865bf5ab3a44185113ba0`.
- Olean: `a94bbd17dfc293ea0c144bb3be4579e6e8debeeda75a40a8039674f3c1511a5c`.
- Log: `06ab9669e98ed763e84bf714754e78c8c92752527dda5dd5d52bc80dd302c7ec`.
- Per-run manifest: `46175481498199e182ce43ce3b71e68fe5502fefb209c9b83c934b746d9179c9`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

## Boundaries

The completed endpoint is about the existing literal V7 Lean codec/map model;
this is not a new Rust machine-code refinement theorem. The distinct comparison
equivalence does not prove a uniform conditional Fiat–Shamir law, bounded-retry
mass, byte-sampler law, or independence from previous transcript queries.
Composition with the separately checked domain and retry leaves is still a
separate task. No payment/row/extraction endpoint, complete soundness result,
privacy claim, CU measurement, or protocol activation follows from this leaf.
