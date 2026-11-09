# PCXA_NONFROZEN: gate modules extracted from a source other than the frozen 4bb3b3f (detector output)

Target not yet established. Detector: Aeneas doc-comment Source line ranges against frozen file text; see detector_limits in the JSON. A flag is evidence of a different revision, not proof; an unflagged module is not shown frozen.

Scanned 258 in-scope emitted modules; flagged 28 (26 in the deployed_splitB cone).

| module | group | splitB | flagged files (definitions differing; blobs matching all ranges) |
|---|---|---|---|
| AdapterRwModel | a | yes | r1_pool_adapter_owned.rs (8; 0) |
| AspisR1AdapterReconstruct.Funs | c | yes | atomic_statement.rs (1; 0); pair_forest_accounts.rs (1; 0); pair_forest_terminal.rs (3; 4); pair_tree_profile.rs (4; 0); pair_terminal.rs (2; 0); lib.rs (4; 1) |
| AspisR1AdapterReconstruct.Types | c | yes | pair_forest_terminal.rs (1; 4); lib.rs (1; 1) |
| AspisR1DecodeKFullV10.Funs | c | yes | r1_wire.rs (3; 0) |
| AspisR1TerminalDecoder.Funs | c | yes | atomic_statement.rs (1; 0); pair_forest_accounts.rs (1; 1); pair_forest_terminal.rs (6; 4); pair_tree_profile.rs (3; 0); pair_terminal.rs (2; 0) |
| AspisR72Sampler.Funs | c | yes | field.rs (26; 0); r23_width.rs (1; 1); r24_guarded_qm.rs (2; 1); transcript.rs (4; 0); lib.rs (1; 1) |
| AspisR72Sampler.Types | c | yes | field.rs (3; 16); transcript.rs (3; 3) |
| ClaimsUnrolledParentSource | c | yes | candidate_claims.rs (1; 0) |
| CurrentCompactCallerTypesV1 | c | yes | state_only_prefix.rs (1; 1) |
| NFG_InverseRef.Funs | R | no | field.rs (1; 2) |
| NFN_ExtractedGeometry | c | yes | field.rs (1; 0); domain.rs (1; 0); verifier.rs (4; 0) |
| NFY_Part043 | c | yes | pair_forest_terminal.rs (4; 1) |
| NGN_Emitted | c | yes | lib.rs (1; 0) |
| NJA_CountBody | c | yes | multiproof.rs (3; 0) |
| NJC_ValidateEmission | a | yes | verifier.rs (1; 4) |
| NJS_Extract.Funs | a | yes | candidate.rs (8; 0) |
| NJT_ClaimsRef_Funs | c | yes | r1_semantic.rs (1; 0) |
| NKJ_Extracted.Funs | R | no | NKJ_reference.rs (9; 1) |
| Port3_NativeBatchBody | a | yes | candidate.rs (1; 0) |
| Port3_NativeGeometryBody | a | yes | verifier.rs (2; 4) |
| Port3_NativePendingBody | R | yes | verifier.rs (1; 0) |
| Port3_NativeQueryBody | R | yes | verifier.rs (2; 0); candidate.rs (1; 0) |
| Port4C_NativePrefix | R | yes | verifier.rs (1; 0) |
| Port5Q2_ReaderValidate | a | yes | verifier.rs (1; 4) |
| Port5Q2_ReaderWeights | a | yes | verifier.rs (1; 7) |
| RPz7_FIo_NativeFuns | c | yes | field.rs (1; 0); transport.rs (2; 0); fast_pairing.rs (1; 0); transport.rs (1; 0); weights.rs (36; 0) |
| RPz7_FIp_NativeDots | c | yes | fast_dots.rs (2; 0) |
| S1NativeCompactModelV1 | c | yes | compact.rs (1; 0) |

Identified by hand: AspisR72Sampler.Funs (M31.mul canonical fast path) = blob a47a9996aa63 of src/field.rs under evidence/r72-sampler/selected/source (first commit 0319ac2b7b5, 2026-09-28). Details and limits in the JSON.
