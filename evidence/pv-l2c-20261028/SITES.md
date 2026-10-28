# D370 current disposition — checked N3 counterexample

Target not yet established. Successful canonical preparation can retain raw
M31(P) at C1[0][444]; native masking preserves it and N3 rejects it, whereas
the same-public M31(0) case passes the exact-body guard diagnostic. The actual
secure prover entry with OS entropy returns Err(Semantic) on the bad case.
Work stopped under the explicit counterexample rule, with 97 Lean attempts
unspent and no new Kani. V352/V354/V357/V360 remain OPEN/P; zero premises
removed, added, weakened or changed. Frozen implementation and HonestInput
are unchanged. Current evidence and accounting:
[resumed finding](resume-d369/D370-FINDING.md),
[state reconciliation](resume-d369/RECOVERY-D370.json),
[native receipt](resume-d369/canonical-n3-probe5/receipt.json).

The earlier dispositions below are historical and superseded by this finding.

---

# Site statements and evidence classes

`native-sites.json` pins the shipped bodies by revision, git blob, whole-file
and body SHA256. A source pin is identification, not a refinement theorem.
`focused-resolution.json` records project import authority; external object
checks and PREFLIGHT-NOTE.md record the exact private view and its corrections.
The final receipt index, not draft status prose, determines accepted targets.

| Site | Proved locally | Required transport still open |
|---|---|---|
| N2 zero/sum guards | PaddingProducer/Consumer: for arbitrary additive group values the negative excluded-sum store forces inactive sum zero and keeps active cells zero. NativeFold/M31/NativeQ/QBalance/QFold: canonical raw word and four-limb additions/subtractions agree with decoded field sums; no initial zero-sum hypothesis. PaddingNative.guard_outcomes: both raw rejection predicates false for any canonical random table and any inactive dependent row. SparseFold.source_sum: literal skip-active loop equals zero-insertion sum. | Actual native sampler/caller table is this table on every HonestInput and honest random tape; native consumer receives that very table and public geometry. Raw-word proofs do not establish this caller refinement. |
| N3 canonical / parser | SampleCanonical: every successful capped scalar/Q scan on any supplied words has canonical limbs, retaining failures. CanonicalParser.scalar_parse: actual extracted scalar from_le_bytes(to_le_bytes x) returns some x when x<P, including the actual byte primitives. | Full compiler/C1/D canonicality reaches native guard columns, native Q parser and column roundtrip, public packed geometry. Kani codec PASS suspended under K-1; no credit. |
| N4 private balances | FirstInactive.table_returned: successful first-false scan returns an in-range inactive index; all-active preserves failure. ReferenceArithmetic/NormalizeSource/ReferenceSub/ReferenceQ: complete actual extracted add/sub result is the literal word/Q operation. VecRead: exact source table/active lookups. ExtractedFold: actual Q-add traversal returns a canonical value decoding to its finite sum. | Honest compiler's precise inactive-set association, packed masks vs bool array, sixteen C1 and both private columns' whole caller transport, actual native equality observations. New selected-row/owned-store modules are only accepted if their final receipts say so. |
| N5 helper short circuits | ExtractedFold.zero_sum gives actual extracted Q-add result ZERO for canonical inputs with decoded sum zero. Existing pv-l2b helper/multiset algebra unchanged. | Honest helper producer/consumer multiset equality, exact native length/table/channel-26 association and nonzero inverse boundary. Zero-sum is still a hypothesis here. No new bad event. |
| N6 sumcheck boundaries | Existing pv-l2b and SemanticModel55 ideal initial/chain/terminal laws are retained, with oracle/interpolation/running premises. | Native oracle on HonestInput, interpolation coefficient association, initial running claim and round-to-round native evaluation. The legacy SemanticGuards55 cohort requires the pinned EJR-compatible private dependency rebuild; the full bridge is not claimed. |

Native mutation fidelity: the Balance9 emission's owned caller applies
`index_mut_back q`; it does not discard the write. `qm31_owned_fold` retains
this continuation and the entire outer Result. The 14-declaration native and
owned-reference differential cut is byte-checked by generate-balance-cut.py.
It is finite validation if run, not universal source equivalence. A structural
(K-1 substitute) full native link needs BOTH a complete-Result reference law
and every representation/control difference accounted for; it is not granted
merely by retaining a source cut. No XR model or compiled object is imported.

Non-vacuity: FixtureAudit states both exact ConsumerBoundary25.HonestInput
fixtures, including the concrete deployed proof field. This shows the carrier
is inhabited; it does not add the guard outcome to its definition or certify
a missing native caller refinement.

## D355 accepted additions and remaining site boundary

* N2: ExtractedGuard.padding_result now composes the complete owned QM31
  Result with both raw predicate outcomes. Native sampler/table and consumer
  transport from each HonestInput/random tape is still missing.
* N3: ComplexParser.parse and QParser.parse now prove the actual extracted
  parser on concatenated canonical scalar-byte encodings. Native secure-word
  writer roundtrip and raw C1/D compiler range transport remain. The decoded
  equality obstruction is formally witnessed by CanonicalityBoundary; this
  is not an honest-input counterexample.
* N4: OwnedBalance.complete_result, ScalarBalance.complete_result and
  ScalarCanonical.output_canonical pass. balance-structural.py binds both
  native cuts to the owned references, with twelve checked bodies and the
  existing finite native differential. The classification is structural
  (K-1 substitute), confined to the balance cut, not every honest caller.
* N5: HonestCaller and HonestHelper now derive total and inactive decoded
  helper cancellation on the exact carrier without a helper-sum assumption.
  Native materialization, channel/table origin and inverse implementation
  boundary remain. HonestValidity uses only the pre-existing NoPole condition.
* N6: HonestSumcheck derives decoded prepared-oracle degree and initial,
  chain and terminal laws on the exact carrier; native SemanticOracle,
  produced interpolation coefficients and running-claim association remain.

Every added theorem is covered by its successful source-matching receipt and
the final combined audit. All 1456 selected source/object/import fingerprints
match. No whole site or row subtraction is asserted.
