# Exact-output work on R18, independent of the channel-fold profile

Base is 77fb78727c8b880b7c029828ad93083ff854f7f6. Use the final minimum-T/base-scaling stage, not the unmodified research templates. Successful source/model tests and successful SBF tests are different evidence levels.

## A. Establish that the internal opening cross-check is redundant

The source report measures 875,150 CU between primary authentication and the internal reference endpoint. Unlike the second complete verifier, this reference is inside the 4,781,147-CU primary measurement.

The algebra is

    ((S-G)-I_R)/L + (G-I_G)/L = (S-I_R-I_G)/L,

followed by the same linear four-slot fold. The independent model verifies these identities on 1,024 full-field cases and detects an incorrect channel perturbation. This does not establish canonical-byte or error-path equivalence.

Required source implications:

- Both readers construct identical source fibre points and line roots from each accepted schedule.
- Selected packed decoding validates EVERY C1/C2 limb used by the reference, including the G limbs accessed separately.
- Batch inverse success and per-record fallback equal the reference at all nonzero denominators. All zero-coordinate and chord-pole cases still reject; preserve the designated error behavior.
- The authenticated leaf byte slices, tags, salts, index order, frontiers and roots are identical.
- Successful primary authentication implies the repeated reference authentication succeeds.
- The reference's reconstructed combined quotient/fold equals the sum of the two primary results for all parser-valid canonical inputs, not just honest witnesses.

On this basis replace ONLY the redundant internal runtime call with a host/CI differential path. Keep the primary canonical/domain/authentication/image/relation checks. A malicious-looking record must not become accepted because a reference check vanished. Use explicit invalid-limb, denominator-zero, wrong-salt, wrong-index/frontier, truncation and altered-final tests. Keep the independent complete host verifier.

Do not count 875,150 as a new measured net saving: compiler layout and instrumentation can move. Also do not subtract the second complete verifier from this already-primary number.

## B. One query accumulator for the existing two-channel protocol

The first channel uses rho^1..rho^22; the second uses rho^23..rho^44 on the SAME line roots. Let lambda=rho^22 and s_i=rho^(i+1). Then

    Q_G = lambda Q_R
    increment = dot(s,values_R) + lambda*dot(s,values_G).

Every later dual fold is linear, hence the equality persists. At the terminal,

    <Q_R,Final_R> + <Q_G,Final_G>
      = <Q_R,Final_R + lambda*Final_G>.

This preserves all 44 batched consistency equations and every old transcript byte. It is not the new channel-fold protocol. It cannot be extended to the distinct ordinary/G base functionals.

Take lambda directly from scales[21], never by division, so zero rho has defined behavior. Install the accumulator only after alpha0 and apply only the three subsequent folds. The supplied model checks all stages, not merely the final result. The Rust helper is an integration draft; preserve source error mapping and source serialization of increment.

## C. Factor the fixed T163 correction

For one tensor w_r=low[r mod16]*high[floor(r/16)], the ordinary correction is the signed permutation operator P-I restricted to 163 coordinates. Many low products recur. The generator groups exact signed entries by source/destination high groups, caches distinct low products, and checks that expanding the tables reproduces P-I over the integers.

The schedule contains 100 distinct normal low pairs, 12 carry low pairs, 92 normal high blocks and 15 carry high blocks. Together with the complete 64-group output contraction, this is 283 logical field products for ONE tensor correction versus 408 in the direct one-tensor construction. That is not a prediction for the whole A/E interval: the current A is itself a sum of two tensors and its existing batching may be more efficient than three separate calls to the draft.

Source implementation should compare both organizations: reuse products across A/E where their point-0 high factors coincide, and preserve the source's sum-products helpers. Stop if actual SBF regresses. All 64 output groups stay present because carry propagation can reach outside the input support. The pivot and fixed inactive-mask contributions remain separate and mandatory.

Use the provided stage inventory gate before installing tables. The generator is based on the retained independent model inventory; it is not a substitute for authenticating the source constructor. Scratch is caller-owned: 112 low cached products plus 128 group entries. Reuse the existing 1024-entry workspace; do not create a 3,840-byte temporary stack array alongside other large locals.

## D. Canonical arithmetic, not a global safety switch

The inspected SBF manifest is already opt-level=3, fat LTO, one codegen unit. It explicitly enables overflow checks. Therefore this is NOT a debug-build diagnosis.

For P=2^31-1 and canonical a,b<P:

    0 <= a+b <= 2P-2 < 2^32
    0 <= a+P-b <= 2P-1 < 2^32
    0 <= a*b < 2^62.

For x=a*b with canonical a,b, x <= (P-1)^2 and (x>>31) <= P-3. Hence s=(x&P)+(x>>31) <= 2P-3 < 2P; one conditional subtraction is canonical. Thus canonical M31 multiplication need not use the general full-u64 double-fold reducer.

The weaker premise x<2^62 ALONE is NOT sufficient for that single-subtraction claim: x=2^62-1 folds to 2P, and one subtraction leaves the noncanonical value P. The packet retains this as a negative control. Do not globally change reduce_u62 on the basis of this multiplication-specific proof.

The general reducer must stay unchanged: four canonical products can have sum above 2^62. Never apply the single-fold helper to a four-term dot accumulator without its stricter range proof. Explicit wrapping add/sub/mul can avoid impossible panic branches in certified canonical-only kernels, but no source speedup is assumed until compiler output and SBF measurements show it.

The draft functions require the real canonical-input invariant. Keep raw-byte validation, usize/index checks and all security errors. Avoid unsafe unchecked arithmetic. A global overflow-checks=false build is not an accepted optimization.

Repeated powers of one-half can use a rotate within 31 bits, with N=0 handled separately. Existing single half() is ALREADY a one-bit rotate; do not present that as new. The optimization concerns repeated halvings/fixed scales only.

Audit the exact selected semantic-carry/boundary and arithmetic cfg chain. Existing source feature optimizations are already substantial; blindly toggling flags is neither a correctness proof nor a CU result.
