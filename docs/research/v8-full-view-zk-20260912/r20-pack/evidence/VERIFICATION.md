# Verification boundary

Executed here, newly implemented independent C++:
200,000 two-lane cases; 53,107 exhaustive reduced-width two-lane cases;
200,000 six-reduction QM31 product cases; 288 complete-dot cases including
lengths 0 through 4096; 2,560 semantic-round/cache cases; 96 complete sparse
terminal comparisons (12 also against a full independent chord adjoint);
2,048 digest-factoring cases; 1,024 beta/gamma cases; 859 malformed rejection
controls, including every one of 152 positions at zero/one/random beta;
a stale-cache negative. Assertions and undefined-behavior sanitizer enabled.

These checks are executed algebraic/word evidence, not a universal proof,
extracted Rust semantics, a source verifier run, SBF benchmark or privacy proof.
Digest event construction and actual qm31_pack_base4 correspondence still
need the source gate. New Rust crate has not been compiled in this environment.
No Lean compilation or SBF tools were available. The linked repository was
read through GitHub; a direct container download attempt failed DNS.

The R19 CU log is source-reported evidence from the repository; it was not
reexecuted here. Its exact commit, source blob and ELF are preserved separately.
The inherited model.hpp came from the prior R19 packet. No old rank run is
relabelled as a new R20 result. New C++ implementations live in new_kernels.hpp
and are compared to that independent model and additional direct formulas.

Small-dot/empty accumulator handling was improved before the final test run.
An assertion-precedence issue was corrected before the first compilation.
Neither correction changed the target field identities or source protocol.

The scalar adjoint and alternate multiplier are unmeasured candidates; fewer
outputs/reductions do not establish lower CU. Failed performance experiments
must remain recorded. No sub-1M result is claimed.

Final checks were also compiled and executed with clang++; its complete output
agrees with the g++ run. Exact integer-range checks and nine synthetic budget-
gate tests pass. Synthetic receipts are explicitly not SBF measurements.
