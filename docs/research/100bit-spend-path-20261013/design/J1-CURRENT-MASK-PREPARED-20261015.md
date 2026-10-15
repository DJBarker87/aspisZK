# Current extracted prepared QM31 multiplier

The optimized multiplier used by the current selected-mask code now has a
checked constructor-to-result theorem. For canonical operands, the extracted
constructor succeeds, its stored arrays satisfy an explicit invariant, and
the extracted prepared multiplication succeeds with a canonical result equal
to multiplication in the retained exact QM31 field.

`PreparedFor` fixes all three inner arrays and the outer array, including the
stored modular sums. The component theorem proves the generated sequence of
three array reads and modular operations agrees with ordinary CM31
multiplication. The final theorem composes the three component results with
ordinary QM31 multiplication and the previously checked exact-field bridge.
It derives the invariant from the constructor rather than assuming constructor
correctness. All caller canonicality requirements remain explicit.

This reuses the six historical pure field/word modules unchanged and the nine
current arithmetic adapters with only their extraction/module names changed.
The [evidence bundle](../evidence/current-mask-prepared-20261015/README.md)
contains 14 successful focused targets, 46 standard-only axiom reports, exact
source/object/import pins, raw resource records, and retained failed attempts.
The maximum successful sampled aggregate RSS was 3,099,264 KiB; all successful
process swap counts were zero. No production Rust source changed.

A direct concrete closure expansion hit the local memory limit. The replacement
isolates its symbolic execution equation before substituting concrete arrays;
it passes at the original cap. This keeps expensive reduction out of callers.

The next actual-source obligations are the selected linear-form recurrence,
basis transforms, coefficient-array population and reverse Horner evaluation,
plus square/scalar operations and the explicit-mask term. Existing reverse-range
and pure mask results have been identified for reuse. Their current adapters
and whole-loop composition are not part of this checkpoint. The full actual
acceptance-to-terminal contract, compiler/extraction, privacy and runtime
release obligations remain open; no complete 100-bit claim is made.

## Integration with the latest lead decision

The fetched [J1.R17 decision](LEAD-REVIEW-J1-R11-R12-20261015.md) requires the
final proof to use Lean 4.32 throughout. This checkpoint's Lean 4.31 results
remain retained component evidence until the pinned Aeneas library and these
modules are rechecked on 4.32. The newly merged Pool/parser work does not
change this extraction's field.rs, wide_exact.rs or state_only_hiding.rs.
The NUC is reachable again; the next host task inventories and ports the
matching library/cache under explicit resource limits. No unchanged full
regression is implied by this integration.
