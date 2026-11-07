# LIBB findings and proof boundaries

Target not yet established. No frozen-source/spec amendment, trust-row change or ledger promotion is proposed by this job.

- L100: simplifying only the outer pair filled call was insufficient because process_kind reaches dense_point_pair's separate filled call. Replacement: isolate dense (L101), process_kind/process_regular (L102), outer pair and installed finish (L103), common normalization (L104). All arithmetic loops stay opaque; no Kani, extraction, cap increase or unchanged failed replay.
- L105: an untyped empty native-record list could not synthesize its H/d/hash indices. Replacement L106 uses the already defined unusedLocations. The contextual frame binds only reached calls and keeps the actual finish ABI locations.
- L110: the new Env module omitted the AspisR1 namespace for the leaf input. Replacement L111 qualifies the namespace; semantic validation is unchanged.
- L115: LIB_Carriers.bytes is the NMS scalar carrier, so its length proof needed that explicit definition rather than the NNC alias alone. Replacement L116 normalizes only the carrier map's length. The four original NMN clauses are unchanged.
- Earlier elaboration failures are retained in their immutable receipts and ATTEMPTS. They are excluded from accepted-source/root coverage; printed sorryAx in a failed elaboration is not accepted proof evidence.

The early LIBB_Tx2Resolved / Tx2TraceModel / Tx2ResolvedValues modules are explicitly resolved-only support, not a canonical field. The canonical-installation work uses LIBB_PartitionEnv / Tx2EnvCode / Tx2EnvTrace instead: resume calls Env.sha256 at the original part list; C04's unambiguous domain-tagged addresses recover that same part list. No partition-invariance law for an arbitrary Env.sha256 is silently assumed. Existing runtime digest realization remains separate.

Module12 still needs one complete graph-of-model law with every independent abort prefix and its canonical Returns/Functional gate on Dom064, tied to the actual host observation. Reached reservation binding is a runtime representation obligation, never an added own-input clause. Generic native/detail/continuation hypotheses in the support modules are not installed as library fields. Module13 is blocked precisely on that field. No Native/Cut/Windows image, empty renderer, arbitrary Ops or child-success premise substitutes for it. The historical determinism-obstruction investigation is not reopened.

## Resume shape repairs

L301: unknown flatten-map name and dependent elimination at an already evaluated C04 reply. Replacement L302 isolates generic indexed Detail before record elimination. L303's direct case-splitting through large source projections is retired: L304/L305 introduce opaque Result projection/observation helper lemmas; L304 only needed the final definitional rfl. L306's parser-level elimination is retired: L307/L308/L309 factor generic Native unfolding and a proof-independent commonExit projection; remaining fixes were keyword `prefix` and final definitional rfl. L310/L311 projection rewrites and reversed Returns transitivity were replaced by the independent observation projection lemma (L312). L313 cannot decide symbolic Usize.max; L314 proves tiny extent bounds with scalar_tac. Every failed receipt is retained/excluded. No timeout/OOM/rerun unchanged/cap increase.

The completed source fold and full-law Returns do not establish whole-Obs Functional. No claim is made that these two propositions coincide. The explicit requested whole-field formula is retained in LIBB_REMAINING.md, pending its interpretation against the frozen allocation-abort exemption; no spec amendment or domain change is applied by this worker.

L322: focused combined import lacked unchanged nested NMT_tx1 objects. L323 changes only the selected dependency environment by copying missing unchanged objects from the merged TX1 pinned seeds; source/object hashes in LIBB_BUNDLE_DEPS_REUSE.json. L323/L324 pass. No shared infrastructure or sibling source was edited.

## Returned-observation gate continuation (bq clarification)

L326 and L330 were explicitly stopped during broad tactic proof search (exit143;33.919s/9188660KiB and63.057s/11422196KiB respectively;swap0). The identical search shape is retired. Its replacement splits generic Safe bind/record lemmas (L328) from a syntactically dispatched source traversal; it never unfolds child calls to discover the constructor. L327 used an incorrect Result.bind identifier, repaired by case analysis on NJU_Log.bind. L329 missed the AspisR1 namespace; L331 introduced the record inequality twice, replaced by an explicit constructor-disjointness proof. No failure is accepted as evidence; no cap or timeout is raised.
