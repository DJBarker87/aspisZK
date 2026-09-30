# R146: exact first callback sequence

The actual selected `before_ood` now equals an explicit sequence from PROFILE,
STATEMENT and ROOT through lambda, chi, SECOND_PHASE_ROOT and the first 358
point claims. Its exact bytes come from the generic serializer proof.

The raw-source theorem works for arbitrary hash functions and retains outer
failure and divergence, callback errors and the returned transcript. A second
theorem connects this whole sequence to the previously proved ordinary sampler
model for any explicit total byte oracle. It retains sampler failure and the
short-input panic; it does not assume successful challenges or 358 input values.

The focused production leaf compiled successfully. Complete proof audits and
resource evidence are retained in `evidence/r146-before-ood-execution`.
`core.fmt.Formatter` remains the disclosed cached generated-source type
dependency; no added proof axiom or unfinished proof appears in the audit.

The next obligation is the later callback sequence and its ordered shared-oracle
history. Privacy and soundness remain open. No verifier source or security
parameter changed, and the existing 999,790 / 999,532 CU result is preserved.
