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

L003: remaining symmetry side condition in reference_eq; corrected by deriving
x!=y explicitly from y!=x. L004 accepts both NHB_Membership top theorems with
standard axioms only. Failed L002/L003 outputs are retained and excluded.
K002: length0 domain with variable slice bound also CBMC timeout90s (exit1,
wall97.751s, process6402712KiB, swap0). Not retried unchanged. K003 replaces
the bound by the domain's literal and installs the prescribed KMX copy stub
annotation. This is a changed reduction shape, with no cap/time increase.

K017: length7 literal-bound positive timed out at the unchanged90s solver limit.
The campaign stops this family; K018 is NOT an unchanged length7 retry. The
0..6 matched contracts remain local facts. The replacement partitions membership
by a model-witness index versus explicit scalar absence conditions. Both domains
must be shown exhaustive before caller credit; no branch is assumed absent or
present at a physical call. Larger same-family length checks are not launched.

K018: absence-partition, arbitrary-length read-only-reference contract timed out
at90s. No unchanged retry. The present-witness partition is an independent
member; it does not rely on the absence result. A further isolated shape uses
an owned fixed-array parameter instead of the contract's read-only reference
carrier; its copy must retain KMX and a matched control. No reference/pointer
semantics are silently replaced or counted as solved by that candidate.

K019: present-witness partition also timed out at90s. Neither partition receives
native credit; neither is used as a stub. L009 proves the model witness,
absence and exhaustive-domain laws with standard axioms. Those logical facts
remain useful but do not turn either native timeout into a pass.

K028: owned fixed22 carrier times out at length11 (90s, no increase). The
0..10 matched contracts remain local facts. K029 changes the interface to a
read-only fixed11 prefix, maintaining the same NHB_contains_11 name and property;
it also times out. No larger same-scalar-remainder check is launched.
K030 pursues the independent block/word cursor association rather than waiting
on membership. A possible remaining membership split uses the actual18-bit
caller invariant; its Lean preservation and decoder-bound obligations are
written and must pass before it can be relied on as a caller precondition.
