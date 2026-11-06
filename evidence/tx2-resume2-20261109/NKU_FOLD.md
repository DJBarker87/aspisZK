# NKU parent fold

Target not yet established. The parent carrier is NKU.State (NKU_State.lean), with one Frame containing the fixed checkpoint/proof/public slices and SAME Reservation; decoded slots, Reader/backing, iterator, owned Vec and full terminal status remain in this carrier.

Events: NKU.Event.call wraps all nine NJU_ResumeObserved event constructors, covering all 45 top-level and nested NKK occurrences; terminal and cleanup are separate parent observations. No new primitive Reader domain is introduced.

NHZ_DRIVER.Cuts uses Code/SdkC_Source.Log, whereas resume uses NJU_Log.Run and NJU_ResumeObserved.Event. A local bind/frame/terminal algebra of the same shape is needed; it must retain fail/div and Rust Err prefixes without suffix.

Status: state defined (pending compile); header first; digests 2–4, roots 5–7, fields 8–12, queries 13–34, validator 35, semantic 36, z/claim 37–43, filled 44, weights 45, tail/Box/pair/cleanup all OPEN. Native component positives/controls are reused only as pinned inputs, never counted as parent closure.

Passing installation: NKU_HeaderStep.source and NKU_Front.source (header1 plus digest2–4, with source suffix explicit). The digest join is NKU_DigestJoin.source. Passing local state steps: NKU_Roots, NKU_Gamma, NKU_QueryFirst/Mid/End, NKU_Validator, NKU_Semantic, NKU_ZClaim, NKU_Allocation, NKU_Weights. Passing terminal helpers: NKU_Array22.source, NKU_Tail.guard_reject. Source-to-state suffix assembly is active; local steps alone do not count as TX2:124 closure.

The complete G is NKU_ResumeRoot.G, with passing source/clauses/cohort equations (L100). Its stage list is header, proof/public/checkpoint digests, roots, gamma, query8/8/6, validator, semantic, z/claim/rhs/power, SAME reservation allocation, weights, terminal guard and construction. Remaining review: replace grouped read carriers by single-occurrence parent-state steps, derive every native window domain from the actual chain, and run combined/raw/scan gates. No row promotion yet.


Final parent: NKU_ParentFold.G (source/cohort/clauses). NKU_FineHeader stores the actual next byte and live bytes[11..16] iterator in the parent record at event1, then ends that iterator's scope before hashes. All raw/E/K calls update that SAME record individually. NKU_CallerScope.header_to_roots proves the earliest full-frame interface; NKU_DigestState proves the full live core survives all three hashes. NKU_SourceConstructors handles the emitted terminal carrier explicitly.

| Occurrences | Final status / association |
|---|---|
| header1, all earlier guards | installed, NKU_FineHeader/NKU_HeaderState/HeaderEnd |
| digest2–4 | installed, DigestJoin/DigestState and SAME immutable Frame |
| roots5–7 | installed, FineRoots/RawAt; Reader80→176 |
| fields8–12 | installed, FineGamma/EAt/KAt; Reader176→320 |
| queries13–34 | installed, FineWords + First/Middle/Last joins; Reader320→408 |
| validator35 | CLOSED child at SAME22 words, QueryLastJoin |
| semantic36 | CLOSED child + full writeback; SemanticJoin;408→568 |
| z/claim/rhs/power37–43 | installed, FineZ/EAt/KAt;568→712 |
| filled44 | SAME Reservation; Allocation/AllocationWidth; no success premise |
| weights45,64 nested reads | CLOSED child on SAME owned Vec64; AfterZ/Offsets;712→1736 |
| guard/Box/pair/cleanup | TailSource/SourceConstructors + retained native value/owner/drop cuts; (aa)/(an)/(au) scope |

Native proof/public scope and incoming C01 clause are explicit in NKU_NATIVE_INPUTS.md. The broader source theorem is not an unbounded native packet. Combined gate1 passed; final gate2 adds the caller-frame and live-iterator statements while retaining exact unchanged-root audits.

Final gates PASS:86 selected modules/124 roots in NKU_COMBINED_IMPORT with NKN_COMBINED_IMPORT, NKK_COMBINED_IMPORT and the deployed headline. Raw ax2 equals collectAxioms, standard axioms only;8 fixtures pass in the final binary; NFX16339 modules/zero issues.99 unchanged walks are retained under the final walk manifest after32917 dependency-object hashes match;25 added roots were walked. Only the combined-import object changed among prior closure objects. Native row is a candidate pending the next ledger gate, with incoming scope explicit. No source suffix remains in NKU_ParentFold.G.
