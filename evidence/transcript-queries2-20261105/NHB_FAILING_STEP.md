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

K032: canonical18-bit fixed11 prefix contract still times out at90s.
K033/K034 test the independent absence/presence directions with owned fixed22
carriers and the caller-proved18-bit invariant; both remain excluded if they
fail. The next split restricts those directions to lengths11..15 and a fixed15
prefix. Its required prefix/canonical/membership adapter laws are explicit.
No shorter passing domain is substituted for full caller coverage.
L016: the set-window rewrite did not unfold the intended Aeneas array carrier;
stopped/continuing fields checked but the module failed. An explicit list
projection replaces the ambiguous rewrite. No failed declaration is credited.

K037: full word/cursor function contract with scalar pre-observations times out
at90s. K038 adds the independently proved inactive-zero invariant (L021), also
times out. K039 specializes to stopped states; it also times out although the
native contains branch is unreachable. Thus these compound limits are NOT
attributed solely to slice membership. K040 removes contract-snapshot machinery
and computes pre-observations in an ordinary source-window harness; still90s.
The replacement K041 separates the already-checked K030/K031 cursor/decode cut
from the SAME candidate's scalar word body. It executes actual native contains;
there is no unproved membership stub. The for-loop candidate binder is the
source association point, not a separately chosen word or digest block.

L018 repeated an own reserved-word naming error (`prefix`); L019 uses `view`
and accepts the generic prefix adapter laws. L020 failed initial list-index and
dependent-index rewrites; L021 uses a typed cell projection and accepts all
inactive-zero laws. L022/L023 exposed only own field-abbreviation/proof-index
elaboration errors in the observation adapter; failed roots remain excluded.

## Final native limits and exact outstanding assertion

K055/K056 establish local length16 membership; K059/K060 establish length18.
K057 passes length17, but K058 times out its control: no credit is granted.
The complete domain still lacks lengths11..15,17,19..21. Scalar/literal/
canonical/inactive-zero and absent/present reductions and source-fused word
reductions are retained in NHB_RESULTS.json; each tool-limit receipt is excluded.
K053/K054 establish only the caller relation for an arbitrary membership Bool:
`reply == coherent_contains(candidate, SAME active survivor prefix)` remains
unproved on those missing domains. It is not a model/native schedule mismatch.
The same-invocation Trace producer and actual_queries cannot be assembled
without that value edge and the reviewed native loop/fission association.
No timed-out shape was rerun unchanged; no limits were increased.

## Loaded-object manifest correction

L033's loaded scan reported zero dangling and duplicate-owner entries but
failed exact import comparison for sixteen NHB modules: the expected manifest
omitted Lean's implicit Init import. The owned source-derived manifest now
includes Init for every non-prelude NHB module, without changing explicit
imports or scanner checks. The old manifest, scan and receipt are retained;
NHB_IMPORT_MANIFEST_REPAIR.json pins the before/after hashes. L034 tests this
changed validation input only; no theorem/root or native replay is repeated.
