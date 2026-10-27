# Declaration comparison status

**Complete release-kit Types/Funs are unavailable.** No equality or whole-function
inequality is established. XRc_cohort_inventory.json enumerates all 45 selected
Types and 87 selected Funs declarations, plus the raw historical 26/36 inventories.
Every declaration is retained for comparison; no highlighted-cut-only coverage
is claimed. Exact source paths, sizes, hashes, kinds, lines and normalized
text hashes are in that JSON. The parser is XRc_inventory.py; normalization
removes comments, attributes and whitespace, without inferring Lean equality.

Selected cohort sources are e5c-union Types b45ee735… and Prepared-only Funs
544b75b9…, as in XRb. The coherent host object's namespace-union origins and
hashes remain recorded in sound-int2's object-source-manifest.json; this job
does not substitute RPz3's c16 source selection. All selected cohort function
and type declarations require release association or justified source-owner
exclusion. Coherent-source resolution and historical-versus-release association
are separate questions.

The inherited source comparisons in ../extraction-repro2-20261027/XRb_Diff.md
remain evidence: verifier.Error has the same eight cfg-selected constructors;
Dot loses count; prepared_claim consumes a 29-power array instead of gamma;
Prepared.new threads mutable scratch; QueryGeometry gains line_z; retired tx1
and tx1_finish differ from candidate.tx1 and query_loop/deferred finish. These
observations are not replayed equality proofs. verify_observed remains opaque.

The same pinned LLBC lacks prepared_claim, QueryGeometry.for_range, checkpoint
and canonical.Dot bodies before this round begins. Thus an exact complete
release declaration-level diff cannot be fabricated from either body metadata
or XRb's partial diagnostics. XRc_001 masks only the requested failing leaves
and fails next in compact.expand_values; XRc_002 additionally masks that child
and fails in candidate.wide_view. Both failures have exact logs/resources.
XRc_003, the final allowed boundary bisection, succeeded (exit 0, 52.066 s,
368544 KiB RSS, zero swap). The output remains INCOMPLETE: required original
body gaps are unchanged. It contains candidate.tx1, query_loop and its loops,
Prepared.new, QueryGeometry.for_query and BatchedWeights.finish with loops.
It does not recover prepared_claim, QueryGeometry.for_range, checkpoint or
canonical.Dot internals. XRc_four_leaves_outputs.json pins every output.

Raw Types: eb031a5234fdf0e3b8335eeb7b635d303af8155e094e69b8abb52c1eab89d67d,
15805 bytes. Raw Funs:
698e6033d4c2bd5f67526fae1e70b1639acc2a7b79a017fb6ce5900b3812ca7a,
169063 bytes. Retained .lean.txt files are unimported extraction evidence.
External templates remain templates; none is an implementation or accepted
proof. TypesExternal requires Windows, ChunksExactMut, WideExact and EbyKDot;
its generated type axioms are NOT added to Lean or promoted to trusted library
substitutions. FunsExternal's placeholders are likewise not installed.

XRc_declaration_diff.json and XRc_INCOMPLETE_*__cohort.diff cover ALL selected
producer declarations and all emitted incomplete-output declarations. Types:
29 cohort-only / 20 release-only / 11 same normalized / 5 different normalized.
Funs: 69 cohort-only / 161 release-only / 9 same / 9 different. Missing namespace
matches are not declared semantic differences. The all-declaration inventory
is a superset of closure use; fresh proof-term reachability remains unproved.

XRc_Association.lean now checks ONE exact declaration slice: verifier.Error,
under a separate XRc_Release namespace, versus the coherent imported cohort
enum. XRc_ErrorSlice.json pins the source declaration and records that only
the enclosing namespace changes. Both constructor-preserving maps are explicit;
verifier_error_association proves they are inverse. XRc_L001: exit 0, 1.174 s,
2641388 KiB RSS, swap 0; #print axioms reports no axioms. No external template
or substituted library is imported, and no top imports this helper.

The full requested typed association artifact remains incomplete: selected
cohort Funs does not define Prepared.new or tx1; required concrete release
bodies are absent and some extracted carriers are external templates. Simply
writing oldNew = project newNew would leave actual declarations, ownership,
dictionaries and both Result/error transports unresolved. Per common rule 4,
stop those items rather than insert desired equalities as assumptions. The
remaining obligations are documented in XRc_OBLIGATIONS.md with affected ledger
families and estimates, but not falsely presented as completed concrete typed
Props for all declaration pairs.
