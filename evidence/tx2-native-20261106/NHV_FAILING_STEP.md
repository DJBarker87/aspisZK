# NHV excluded attempts

K001: frozen-scratch compilation stopped at missing literal #[path] input
 tools/r1-builder-reference/tree.rs before the NHV harness compiled. Own staging
input omission, not semantic failure or host infrastructure. Added all frozen
r1-builder-reference .rs inputs with exact hashes, no dependency/lock/feature
change. No timeout or memory kill; no success credit. This does not modify or
repair the shared NHR stager. Runner construction also had one local syntax
error (elf/elif), fixed before submission, no host attempt.

K002: own harness type error: QueryGeometry inverses are Vec<[M31;5]> and line_z Vec<M31>, not E vectors. Corrected to the actual field types and the TX2 twelve-entry geometry shape. No solver verdict or credit.

K003: resume whole reply with simultaneous dynamic Prepared and Accumulator field projections timed out at90s (scope93.660s, peak3958208KiB, swap0). Excluded. Replacement first isolates exact arguments, full error transport, split guard and owned Box/weights identity; field projection facets are separate obligations. No raised cap, no unchanged rerun.
