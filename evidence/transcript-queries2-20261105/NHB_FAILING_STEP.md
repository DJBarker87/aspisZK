# Retained failures

L001: own inspection used two nonexistent names; import and other printed
interfaces succeeded. Corrected inspection source; no theorem credited.
L002: own Lean statement used reserved `prefix`, dependent congrArg decide,
and a redundant simp. Source/errors retained in L002. Unsuccessful elaboration
printed sorryAx; it is excluded, never accepted as a theorem or standard audit.

K001: variable-length slice membership contract against a scalar reference loop
CBMC timeout90s, scope exit1, wall97.627s, process peak6349216KiB, swap0.
No credit and no unchanged retry. Replacement: length-specific contracts for
all23 possible prefix lengths with a straight scalar reference disjunction.
This is a tool limit, not a source/model schedule mismatch.
