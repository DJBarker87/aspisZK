# Unified fresh-attempt composition evidence

The target `R1UnifiedFreshAttempt` composes `UnifiedEventDensity.density_bound` with `FreshAttemptBound.thirty_three_hitMass_lt`. For every current prefix, message, table, and row index, it instantiates the density theorem at `P.rounds.length` and uses the sampler-prefix identity by reflexivity. This supplies the density input to the existing 33-step fresh-answer theorem while keeping arbitrary before-row message selection and table updates explicit.

The result is a conditional fresh-row-sampler bound. It is not a memoized/shared-ROM statement and proves no acceptance, source correspondence, or new density premise. The reused adaptive-union result over per-history finite bad sets and the exact sampler API are documented in the prior FreshAttemptBound bundle.

Source base: `8e6c2b4cba1c54fe165f7436f5fc3ada1e1ae0f3`. Attempts a/b are retained; a failed proof plumbing and b is green. Receipt b records exit 0, 2.12 seconds, peak RSS 3,591,360 KiB, zero swap, and a 4 GiB high / 6 GiB maximum / zero-swap / 128-task cap. The theorem has only standard axioms `[propext, Classical.choice, Quot.sound]`. The object archive contains only the final target. Both imported source/object pins, runner and environment are recorded.
