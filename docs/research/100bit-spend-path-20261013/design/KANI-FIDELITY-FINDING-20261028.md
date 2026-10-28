# Finding K-1: the pinned Kani verifies a false memory-copy property (lead, 2026-10-28)

Sources: evidence/kani-diag-20261027/KDX_FINDING.md (KDX_, merged),
evidence/native-tx1d-20261027/NBM_COPY_FINDING.md and
evidence/native-tx1c-20261027/NBJ_COPY_FINDING.md.

## What was shown

Tool pins: cargo-kani 0.67.0 / CBMC 6.8.0, frozen source 4bb3b3f5..., frozen
lock 5782e6a3... The harness copies a 16-element u32 slice into a zeroed
16-element array with `level[..n].copy_from_slice(&input[..n])`. On the
fixture input[7] = 1, input[15] = 512 (others 0), n = 16:
- Native execution, including the Kani-generated concrete-playback test,
  gives level[15] = 512.
- In Kani, CBMC's builtin memcpy is called with n = 64 bytes, and after it
  the trace shows level = [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]: the last
  element is lost.
- With #[kani::unwind(17)] and explicit --unwinding-assertions, the false
  assertion `level[15] == 0` is VERIFIED (KDX_K029: 0/37 failed). That is a
  reachable false-property PASS.
- An adequate unwind bound does not remove the divergence (KDX_K001/K002),
  and neither does --no-array-field-sensitivity (KDX_K030).
- The internal root cause is not yet established.

## Consequence

Every native P6 leaf and bridge rests on Kani PASS results. A PASS of a
harness whose asserted property depends on the result of a reached memory
copy (copy_from_slice, clone_from_slice, copy_nonoverlapping, array or slice
clone, to_vec, extend_from_slice, ptr::copy, or Vec growth reallocation) is
not reliable evidence under this tool pin until shown otherwise. This is a
trust-boundary finding: the hybrid P6 method trusts Kani's soundness, and
that soundness is now contradicted for one builtin.

## Immediate correction (accuracy; no permission needed)

Credit is SUSPENDED for every Kani PASS in which a reached copy builtin's
result affects the asserted property, and for every leaf closure or bridge
that depends on one, until re-verified without that builtin. The KDX_
exposure table lists the reached-copy harnesses; it covers stages of
compact::expand_values (LPa_/LPg_/LPh_/LPl_/LPn_), verifier::checkpoint
(LPe_/LPi_/LPm_), candidate::wide_view (LPa_K015), decode_k (LPn_K010) and
the prepared_claim stages (LPb_/LPe_). The affected leaves are therefore
suspended until re-verification: expand_values, checkpoint, wide_view,
decode_k and prepared_claim. Harnesses whose only copy-name match is an
identifier collision (marked "call-name overapproximation" in the table)
keep their credit. Stages that reject before the copy on the admitted domain
(LPa_K005/K007, NBE_K005) also keep their credit.

## Mitigation (no new trust)

1. Pin down the exact trigger: element type and size, copy length relative
   to array length, offsets, last element versus others, slice versus array
   destination. This fixes the true exposure.
2. Replace every copy builtin in harnesses by a stub implementing an
   element-wise loop (kani::stub), and validate each stub three ways: Kani on
   small sizes, a native differential, and a Lean statement of its meaning.
3. Re-run every affected credited harness with the stubs; credit is restored
   only per harness, on a pass under the stubs.
4. For information only, run the reproducer on a newer Kani/CBMC; no version
   change is adopted without the owner.

## Owner decision requested

The trust inventory should record that Kani 0.67.0 is trusted for P6 bridges
only for harnesses with no reached copy builtin, or with copies replaced by
validated element-wise stubs. Recommendation: adopt that narrowing; it adds
no trust and keeps the pinned toolchain.
