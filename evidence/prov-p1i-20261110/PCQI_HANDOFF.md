# PCQI_ HANDOFF: phase P1i (frozen route for definitions with no fresh emission)

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; nothing pushed. Frozen 4bb3b3f. Branch codex/pc-prov-p1i-20261110. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p1i-20261110/. Extraction 7/40 scopes, Lean 27/40, one at a time, caps unraised, swap 0.

Finding first: gate R1CandidateWideParserSource WideExact.from_le_bytes has a different body from frozen wide_exact.rs from_le_bytes (QM31 halves vs eight limbs + from_limbs); fresh = gate not closed (PCQI_L012). Not shown semantic; OPEN (PCQI-C6).

Claims (each exit-0 scope, standard axioms): 49 of the 325 NO_FRESH_EMISSION definitions now EQUALITY_PROVED at ON (PCQI_PROVED.json, PCQI_ALL_STATUS.json: EQUALITY_PROVED 945 -> 994, OPEN 617 -> 568): CurrentWideMulCanonical (3), AspisR1CurrentWide WideExact ops (5), AspisC2HostEmbedding (3), EqualityValueSlice QM31.sub, FIp_DotDecode/CandidateFieldParsers from_le_bytes (6), WideParser BYTE_LEN, V8R19 Guarded/Complex/Quartic inv+square_n (12), Stage2 for_range closures (6), Native01/V7 PartialEq eq (3), NJA/DecodeK/ClaimsUnrolled/PublicPreparation/Circle Types (11). Reused pinned ON emissions from P1g and P2j for several (PCQI-C3).
Assumptions: none added; library models (Option.branch etc.) recorded as DEPENDS_ON_LIBRARY_TRUST (PCQI-C13).
Not done: 276 remaining in PCQI_REMAINING.json (35 with an ON emission already pinned but not yet compared, e.g. NMT_first, FinishCandidateExplicitOps.folds, NJC Reader.raw, CurrentCompactCaller*; the S1M31EmbeddingSourceV1 source_from_m31 and the wide cut modules otherwise have no frozen emission attempted). Weights.raw closures need an Array-mapping Equiv (not written).
Next: compare the 35 pinned-but-uncompared emissions; Reader/View types; weights Equiv.
