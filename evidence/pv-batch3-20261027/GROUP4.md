# Group 4 candidate: mask117 / polynomial121

New module crates/aspis-prover/src/host_arithmetic.rs is behind `#[cfg(feature="prover")]` in that crate's lib.rs. It copies only the selected mask arithmetic, its exact private coefficient tables/linear/tower/power helpers, and the selected block polynomial evaluator. No core/statement function is changed. The same explicit prover feature was already forwarded by cost-probe.

Changes to arithmetic shape are control-only: range iterators become index loops in the same order, including descending coefficient/Horner indices; the op121 block closure becomes an explicit function with polynomial and powers arguments. All field operations, grouped product3 operations, prepared multipliers, coefficients and error boundaries retain their original order. No naïve Horner substitution or raw-limb normalization is introduced.

Redirected selected chains: host_semantic mask-value evaluations and copied terminal masked evaluation -> host_arithmetic::state_only_selected_mask_value; host_sumcheck round update -> host_arithmetic::evaluate_state_only_polynomial. In aspis-prover, state_only_hiding's selected mask consumers and state_only_zerocheck's selected round update use cfg-selected imports; non-prover builds retain the originals. Historical non-selected candidate/reference paths are retained.

D234/V403 remains a required proof obligation: canonical coefficients/challenge must be derived from their actual reached producers, never inserted into T or disguised as a proved hypothesis. The copy preserves the selected block evaluation exactly, so arbitrary-raw-input source equality is a structural question; the polynomial row/model interpretation remains on PV_Canon's canonical carriers. No row/source/domain theorem is yet claimed. Kani0 throughout.

Group 3 passed all pins and projects cumulative +1.64609% worst fixture, leaving 50,892.33us before the +2% stop threshold. Group 4 gates pending.
