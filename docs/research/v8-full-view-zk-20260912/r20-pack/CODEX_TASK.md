# R20: close the execution gap without another privacy-profile change

Base c9315d8b05efb2cdad976bb0f4db3574f1c24577, branch
research/v8-r19-channel-fold-20260921. Preserve this measured endpoint.
Create an isolated working branch; do not change production or deploy.
The objective is a COMPLETE verifier below 1,000,000 CU, not 1.4M, not a
checkpoint, not split transactions and not a higher-cap acceptance relabeled.
No claim that this packet already achieves that objective is authorized.

## A. Reconcile and attribute the actual machine

Read R19_CHANNEL_FOLD.md and the pinned actual primary logs. Reconstruct or
reuse the accepted canonical-a stage. Verify its source manifest and ELF.
Run tools/audit_stage.py on it. Repository r17_host_relation.rs is a TEMPLATE;
do not optimize an obsolete path which the measured assembled verifier does
not call. Retain the source flags, but verify actual emitted call sites:
v8_qm_hybrid/v8_qm_lazy_c0/v8_prepared_schoolbook are NOT proof that a new
standalone kernel reaches an optimized implementation.

Record fine checkpoints, in a separate diagnostic artifact, for:
* semantic compact rounds versus payment terminal; inside the latter, Copy,
  Poseidon, public-digest and mask contributions;
* preparation gamma batches, selected interpolant entries and descriptor;
* record decode, gamma/C2 recombination, quotient/fold and leaf hashes;
* ordinary tensor construction, T163 correction, grouped inactive correction;
* G coefficient generation, geometry and contraction.
Run a clean uninstrumented complete primary for the acceptance number.
Do not count removal of a duplicate reference again: both known duplicates
are already absent from the fastest R19 execution.

Before a new full proof/certificate campaign, use the actual active Rust
kernels to measure generic multiplication, prepared multiplication, 3/4-term
dots and representative 6/16/27/163-term contractions. Keep all old and new
micro results; use full-verifier A/B to select, never host timing alone.

## B. First same-proof candidate: beta-weighted gamma

Implement the identity in design/MATHEMATICS.md using a coefficient-only
prepared view. Weight C1, H1 and D by (1-beta), G by beta. Prepare once after
beta, without modifying transcript order. Hoist the mixed interpolant too.
Retain existing partial-reduction mixed-width C1 dots; the isolated portable
Rust gamma.rs is not a reason to replace them with slower generic products.
Avoid re-decoding G after the complete canonical decoder has already read it.

Source controls: all 152 noncanonical positions at beta 0,1,-1 and arbitrary
QM31; arbitrary authenticated records; both interpolant branches; every pole/
zero/domain error; current entire malformed-input corpus. Do not skip checks
when their algebraic coefficient is zero. Leaf inputs must remain byte-identical.
Use the SAME two R19 proof fixtures. Verify exact values before/after folding.
Measure and retain the result even if it regresses.

## C. Main execution experiment: whole-kernel linear arithmetic

Integrate the nine-channel whole-dot accumulator as a source-local helper.
Audit caller factor canonicality. Validate private canonical representations
once at the actual kernel boundary, not with an extra dynamic guard before
every field operation. Do NOT modify the general public M31 tuple API to
silently accept different invalid inputs. No global overflow-check switch.
Keep the full-u64 reducer and all four-product integer bounds.

Compare old scalar accumulation, existing prepared small dots and new whole
dots at each hot contraction; choose by SBF measurements. Process sparse
normal/carry groups sequentially; never put 64 Dot structs on the SBF stack.
Reuse caller scratch and retain pointer/capacity checks. A dot of size <=4
must not be penalized by a needless large-dot path.

The standalone private Q type and 16-product/6-reduction multiplier are
COMPARISON BACKENDS, not automatically novel versus staged R19 or the chosen
source implementation. Read the staged hybrid/lazy code before spending
an experiment on an already implemented formula. Do not substitute an
uncompiled standalone crate as the production field library.

## D. Semantic terminal, not just PCS

Source-bind the event factoring against public_digest_packed_selector_tensor
and append_level(s)_packed_selector_tensor. Construct the event inventory from
the current source, preserving optional recipient, all 20 levels, the carry
boundary, actual empty roots and every domain tweak. Pair the same local0/11/12
selectors with the same residual groups. The supplied generic 3-group model
is an algebraic control, not a claim its event builder already matches source.

Test arbitrary opened QM31 arrays (not just valid witnesses), extrema of
next_pair_index, carry 0/19/20, both public payment variants where supported,
and every optional-event branch. Compare all lane outputs, not only a final
batch that could hide a mismatch. Replace immutable large by-value interfaces
with references only after preserving call semantics. Inspect emitted code;
do not claim every old value argument was necessarily a physical copy.

Then compare semantic block-Horner + G recomputation with retained semantic
basis + whole-dot + later cache reuse. The latter must cache the ACTUAL ten
challenges and retain all 271 coefficient identities. Allocate 4320 bytes in
caller storage, not a stack return. Include alpha=0/1, all-max coefficients,
and stale/reordered cache negative controls. Count work moved into the earlier
phase; no free-saving claim from deleting its later duplicate.

## E. Share terminal geometry and audit scalar contraction

Ordinary and G use the same abc and all four relation alphas. Share their
normal/carry/high geometry and any common powers once, preserving T163,
pivot/inactive correction and ALL image terms. The supplied scalar transpose
is an independent oracle and optional benchmark, not a default faster path.
It can use MORE products: reject a measured regression.

Controls must include arbitrary canonical final arrays and arbitrary image
residuals; do not restrict to generated-valid quotients. Neither challenges,
query count, code rate, G coin slots, T163 nor proof messages change here.

## F. Mandatory acceptance and evidence

Run current canonical, malformed, authentication and semantic negative suites;
run both genuine source fixtures and additional independently generated ones.
Preserve full host differential verification. On SBF run under an actual
1,000,000 cap with the same 256 KiB heap and complete primary. Resource failure
is not rejection. Preserve each candidate's compiler flags, sources, ELF and
fixture hashes. No unvalidated table supplied by a prover, no omitted image
or relation check, no native-host substitution.

Use tools/check_budget.py on a receipt conforming to its schema. This is a
finite benchmark gate, not a universal resource or security proof. The current
source record MUST fail that gate. Under-one-million success remains false
until a corresponding real complete run exists.

If no measured combination reaches 1M, do not mark this complete and do not
invent a 3x multiplier from logical-operation counts. Commit the best exact
variant and the residual cost breakdown, with the target still OPEN. Explain
which component remains above its budget; don't immediately change the privacy
protocol again. Keep universal source privacy/soundness obligations separate.
