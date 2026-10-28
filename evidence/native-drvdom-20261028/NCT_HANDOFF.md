# Driver-domain audit (stage 1)

Target not yet established. This lane is Lean only; no native gates run.

Before: `KNE_Caller.DriverEstablishedDomain Reached := ∀ p a,
Reached p a → ∃ pm am, S1S7S8StateProvenance p a pm am`.
`Reached` is an arbitrary predicate supplied by the enclosing caller, not a
native reachability definition. Its p/a carriers are the checkpoint writer's
Prepared/Accumulator. Existential pm/am are their exact numeric field
interpretations, not independently fixed transcript/model states.

Provenance contains S2, 64 weights, all 22 queries <262144, CanonicalFields
(gamma/kappa/alpha/rho/semanticAlpha/coordinates/claim/rhs/power/weights), next10,
and equality to the SAME interpreted pm/am. It does not itself assert final_len;
KNE_Schedule.caller_final_len derives 64 from S2 transport arithmetic.

NCL_DriverCuts.accepted covers one emitted CurrentCaller candidate.tx1 with
observer none, successful `ok (.Ok saved)`, and OFF_FOLDED_ROOT=7751,
OFF_ROUND1=7783. It derives split10 and cuts of that same call. The dictionary,
digest, semantic/public/proof/hash and saved Vec stay indexed together.
NCL_DriverForward.source replays precisely those cuts at split10; it adds no
state canonicality guarantee. On arbitrary Ops, the child operations are
abstract. Installed Configuration still contains abstract preparation and
query primitives. Neither theorem's conclusion is a provenance record.

The strongest available control theorem Tx1Q_Control.fields derives weights64,
next10 and canonical flushed weights from installed query/pending/flush calls.
This is smaller than CanonicalFields for every writer field. Accepted-run cuts
also do not establish reachability for calls in runs that later reject/fail/diverge.
No all-native-reached-calls claim is made.

Plan: check the co-import and exact printed statements; derive installed model
control from NCL cuts without reproving child facts; explicitly retain any
unproved S2/query-bound/full-canonicality gates in the strongest composition.
Native/model call identification remains the open owner transport decision in
`docs/research/100bit-spend-path-20261013/design/COMPOSITION-TRUST-DECISION-20261028.md`
or the driver's own native bridge. This packet cannot adopt that decision.

Stage-1 validation: NCT_L001 compiled NCT_Audit.lean with the actual co-imports;
exit0, 2.221831s, peak RSS5347848KiB, swaps0, revision4e647af907.
The printed roots use only propext/Classical.choice/Quot.sound. Full statements
and receipt are NCT_L001/stdout.log and NCT_L001/receipt.json. Both seed caches
were COPIED to the own retained cache; per-file source hashes are NCT_CACHE_COPY.json.
No shared cache was written. This focused audit is not a release replay.
