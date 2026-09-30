# R140: exact nonzero source/model bridge

Source base: `cb23cfb8dd6937fb09fc6ba1c8df1f581e5d79fa`.

R140 closes the deterministic correspondence for the exact R137
`challenge_nonzero_qm31` wrapper.  It proves:

- encoded canonical words equal zero exactly when their source naturals do;
- the encoded QM31 value is source zero exactly when all four limbs are zero;
- the generated nested `PartialEq.ne` implementation returns `false` on that
  tuple and `true` on every other canonical four-limb tuple;
- every finite nonzero retry recurrence preserves inner exhaustion, accepted
  value, outer exhaustion and advanced transcript state relative to
  `BoundedSamplerWrapper.run`;
- at cap three, the actual extracted nonzero wrapper equals
  `SamplerWrapperPolicies.nonzeroRun` after the explicit result encoding.

The focused NUC leaf compiled under the 5/7 GiB cgroup at 2.20 seconds,
3,711,056 KiB peak RSS and zero swap.  Its printed axioms contain no
`sorryAx`.

The first remaining source-specific proposition is now callback-level
chronology: instantiate the actual absorb/nonzero sequence for gamma, kappa
and tau against the selected relation-prefix program.  The q22 source bridge,
actual oracle admissibility, privacy and soundness remain open.  No verifier
source or CU endpoint changed; the selected verifier remains **999,790 /
999,532 CU**.
