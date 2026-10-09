# Typed compact/query/image recurrence — kernel-checked boundary

`experiments/TypedRelationTerminalV3.lean` is kernel-checked. Source SHA256 is
`05a8ea8a361cbb09fa426287d37f446b3123329e9b7bf46d88dda726ff4be9a3`.
It has eight standard-only axiom audits, imports only `CausalOrderedRelation` and
`CanonicalRelationInput`, and keeps recursion depth200 / heartbeats200000.
No local Lean or cache build was run. Source parent is
`d879105131a34a4bd087409bced83778d3ea8a96`.

## Exact checked endpoint

`Fields` has response0 as a function of tau, final256 as a function of
tau/alpha0, and a tail selected only after the ordered queries and rho.
`TailFields` explicitly has response1, response2(alpha1), and
response3(alpha1,alpha2). Its `raw` is constructed from the existing
`RawRounds.step` three times and `done 4`; it supplies no success predicate.
`Fields.strategy` constructs the existing ideal `Strategy` from these fields.

`source_accepts_iff` proves:

```text
sourceAccepts(actual snapshot, same final256, ordered query points,
              oracle.folded alpha0, rho, same typed tail, alpha1,alpha2,alpha3)
  ↔ CausalOrderedRelation.accepts
      pre oracle fields.strategy tau alpha0 queries rho [alpha1,alpha2,alpha3].
```

The left side is an explicit scalar comparison: the dot of the deferred
ordinary and query terminal weights with the folded final256, plus the
carried image scalar times final[3], equals three successive compact Horner
evaluations of the post-query claim. It is not an assumed correspondence
field. The first compact response also has its literal Horner value exposed
by `first_claim_horner`. The image equations and query residuals can be wrong:
no such zero hypotheses occur in this theorem.

The kernel work beyond the existing compact algebra is:

- `last_fold`: generic last-index transport under a dual arity-four fold,
  without enumerating any layer;
- `image_first_fold`: the three image weights at1021/1022/1023 fold to one
  weight at255; all other fibres vanish by index bounds;
- `post_terminal`: propagate255→63→15→3, reuse
  `ImageCallbackInterfaces.sparse_image_terminal`, and split the ordinary
  and query contributions using linearity.

The resulting exact scalar is

```text
(alpha1*alpha2*alpha3/256)
  * (tau*alpha0 + tau^2*(b*alpha0^2-c*alpha0^3)).
```

The factor1/256 comes from four dual folds, not three. The initial three
sparse weights are `[0,-tau²*c,tau²*b,tau]` in the last four-entry block;
the dual powers are `[1,alpha0³,alpha0²,alpha0]/4`. Only this one small block
is expanded. `fold_add` is a narrow symbolic port of the identical theorem
in `V5RelationStressSourceBridge`; its broad source schedule is not imported.

Query weights start at dimension256 **after** alpha0. They are not chord
transposed and do not receive a first fold. Both scalar and weights use PLUS
updates with rho^(j+1) in the original query ordinal order. Therefore the
existing `PostQueryFunctional.post_discrepancy` applies to the same `p`,
`final`, `points`, `received`, `rho`: its residual is exactly
`lineEval final (points j)-received(points j)`, subtracted from the prior.
Sorting authentication entries is not permission to reorder this sum.

## Decoded fields and adaptive ordering

`Decoded.fields` constructs these inputs directly from response buffers with
the appropriate causal function types. It uses
`CanonicalRelationInput.response` at rounds0/1/2/3, hence the actual stored
offsets417/423/429/435, and final256 at441+i. Response2's buffer may depend on
alpha1 and response3's on alpha1/alpha2. The final buffer may depend on
alpha0 but has no query/rho argument. The constructor does not require all
buffers at different histories to be equal, or embed one whole wire as a
constant strategy. `response_fields` and `compact_boundary` reuse the checked
697-field projection and omitted-quartic rule. `source_accepts_iff` applies
to this constructed `Decoded.fields` without a supplied terminal equality.

The compact rule is the existing V6 relation grammar: six sent coefficients
occupy0,1,2,3,5,6; coefficient4 is `claim*quarter-c0`. The successful-source
arithmetic interpretation must still identify quarter with the source's two
halvings. `CanonicalRelationInput.decoded_boundary` consumes the explicit
`quarter*4=1` check. The recurrence equality itself does not need to assume
that an adversarial compact polynomial is honest.

The source flow remains the corrected V8 flow from the previous source map:
C1 → lambda/chi → C2 → theta/zerocheck-point/mu → eta → ten semantic rounds
→ ordinary claims/semantic check → sequential OOD answers → gamma → inactive
→ kappa → tau → response0 → alpha0 → final256 → queries → rho → later
responses/challenges. No Tag73 V7 schedule theorem is substituted for it.
The structured v2 functional framing remains distinct from the dense-vector
framing; this leaf equates field-level recurrences, not transcript bytes.

## Exact remaining source interface

The shifted inactive-plus-three-MLE ordinary functional enters as
`Before.ordinary`, with its corrected claim/chord coefficients. This leaf
does not yet prove that the current Rust `Description::terminal`, masked
weight construction, packed openings, or mutable `Wire` decode to those
inputs. Its `FixedOracle` argument is an existing typed object; it does not
derive total C1/C2 words from two finite-root commitments.

To reach `verify_parsed success → idealAccepts`, retain the obligations from
`selected-accepted-prefix-partition-review.md`:

1. source/typed parse, actual QM31 operations and successful inverses;
2. authenticated fixed-total-word provenance, or explicit collision branch,
   establishing the same folded query openings;
3. actual shifted mask/MLE/chord construction and structured terminal
   implementation agreeing with the typed ordinary functional;
4. prefix-respecting selection of the decoded buffers throughout the
   adversarial continuation family.

Those are not silently replaced with `same_prior`/`same_terminal` premises.
Conditional on constructing the typed inputs, the new leaf discharges the
compact scalar/query/image recurrence comparison. The
existing accepted-prefix partition then applies; no acceptance→HighPrefix
claim, new gamma count, source sampler law, FS freshness, or payment theorem
is added here. Concurrent sampler and payment files are untouched.

## Focused verification and retained dependency restoration

| Source target / exact tag | Exit | Wall s | RSS KiB | Swaps | Outcome |
|---|---:|---:|---:|---:|---|
| `TypedRelationTerminal` / `typed-relation-terminal-nuc-v1` | 1 | 0.93 | 2100016 | 0 | Missing `CanonicalRelationInput`; no theorem elaboration credit. |
| Same / `typed-relation-terminal-nuc-v2` | 1 | 0.89 | 2099972 | 0 | After restoring Input, missing `CanonicalCollect`; no theorem elaboration credit. |
| Same / `typed-relation-terminal-nuc-v3` | 1 | 3.56 | 6699416 | 0 | Opaque Fin numerals, rewrite matching and an unexpanded terminal wrapper. |
| `TypedRelationTerminalV2` / `typed-relation-terminal-v2-nuc-v1` | 1 | 3.44 | 6696172 | 0 | One remaining opaque finite-index equality; other repairs cleared. |
| `TypedRelationTerminalV3` / `typed-relation-terminal-v3-nuc-v1` | 0 | 3.94 | 6729772 | 0 | Eight audits, all standard-only. |

The first two reruns corrected missing environment artifacts rather than
replaying unchanged settled mathematics. V2 used explicit `Fin.mk` indices,
pointwise `congrArg` instead of rewriting under a lambda, and expanded
`ordinaryTerminal` before ring normalization. V3 changed only the remaining
finite-index proof to `Fin.ext (show i.val=255 by omega)`. No cap or theorem
premise was increased. Earlier source versions and all fifteen exact
source/log/manifest artifacts are retained; failed sorryAx results receive no
theorem credit. Import **V3** only: the three versions share a namespace.

Successful digests:

```text
source/snapshot 05a8ea8a361cbb09fa426287d37f446b3123329e9b7bf46d88dda726ff4be9a3
olean          ab7f519f9f4820b81b2479778b828d4bfb551db34a79268f370181779b1b51d8
log            9a1d1ca3b75668c161b7e3c93884c77a7811a18ded351e9cced4ee215b29c7c3
manifest       00d86bf0569a13d89f32d198b3689acd41b4be9dd89f67d107d2caa7eeb07c2d
```

Audited exports: `last_fold`, `image_first_fold`, `post_terminal`,
`first_claim_horner`, `tail_accepts_iff`, `source_accepts_iff`,
`Decoded.response_fields`, `Decoded.compact_boundary`. Each has exactly
`propext`, `Classical.choice`, `Quot.sound`. Six unused-section-variable
warnings and one redundant-`<;>` style warning are retained, with no successful
error/sorryAx. They were not silenced or used to justify another replay.

The inherited scope is `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`,
runner parent289d7356, borrowed26a9cd47, Lean4.32.0 Linux commit8c9756b2.
Every log records `-j1 -M9500`, MemoryHigh8589934592,
MemoryMax10737418240, MemorySwapMax0 and CPU200%. Access and artifact transfers
used Tailscale `dombarker@100.108.41.90`, BatchMode, ConnectTimeout10,
StrictHostKeyChecking, and HostKeyAlias=nuc.local for the key only.

The successful log records 1053 registered entries unchanged before/after.
**Both restored parser modules are absent from all five run manifests.**
Their source/output pairs were separately hash-checked remotely after the
run at2026-09-11T11:42:05Z, against the local retained bytes and the original
green `canonical-collect-v2.log` / `canonical-relation-input-v2.log`.
Full hashes and the exact observation are preserved in
`experiments/typed-relation-terminal-restored-dependencies.txt`.
The old parser receipts used the same Lean4.32.0 commit and Mathlib revision
on macOS; the present Linux import succeeded. These are reused dependency
proofs, not eight-plus-thirteen new audits. No historic manifest was edited,
no missing per-copy receipt reconstructed, and no complete cross-platform
transitive-import equivalence claim is inferred from the registered-entry
check. `canonical-relation-input-review.md` retains the original scope.

Read-only audit (no Lean/cache/SSH replay):

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_typed_relation_terminal.py --check-recorded
```

The scoped evidence JSON records one green target / eight standard audits /
five attempts / four failures, with separate restored-dependency provenance.
Ignored oleans are optional in a publication clone, but their hashes are
verified whenever present. Whole Rust/source/FS refinement remains open.
