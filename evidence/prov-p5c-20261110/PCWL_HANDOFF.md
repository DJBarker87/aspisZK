# PCWL_ HANDOFF (job pc-prov-p5c, phase P5c, OPEN definitions, second module batch)

No ledger row, trust row, RSL, security contract or shipped source changed; no trust row proposed; nothing pushed or merged. Frozen source 4bb3b3f. Lean scopes 27 of 35 (all one at a time, 6G/8G, swap 0, caps unraised), extraction scopes 6 of 10. Tables: PCWL_STATUS.json, PCWL_REMAINING.json, PCWL_TRIAGE.json, PCWL_CLASSIFICATIONS.json, PCWL_TOOLS.json, PCWL_ATTEMPTS.jsonl, receipts PCWL_Lnnn/ PCWL_Ennn/.

## Differences first
1. AdapterRwModel.owned.require_zero: the gate loops by index, the frozen function loops over `remaining = &remaining[1..]`. A source difference, not an encoding difference. Values agree for every slice (PRVEq.AdapterRwModel_w7.require_zero_eq, proved). The gate's require_zero_loop and its body have no frozen counterpart and are cleared only through that parent.
2. The compiled AdapterRwModel (L187 objects) is not the repository source with sha 11679ad2 that the generator inputs carry: compiled Pubkey PartialEq is `eq := ops.op36, ne := PartialEq.ne.default`, the source has `ops.op38` and `trait_default`. Statements here are against the compiled constants.
3. require_distinct_accounts: the gate adds with wrapping_add on the index (OFF shape); the frozen build here is ON. Unresolved: no fresh text exists.

## Per module (definitions SETTLED / still OPEN)
* AspisR1AdapterReconstruct.Types: 11 of 11 settled. PRVEq_AspisR1AdapterReconstruct_Types_w1.lean (PCWL_L001, exit 0, 5.9 s, 2.6 GiB). Type isomorphisms against emission PCWE_E003 (original Aeneas, ON). The generator could not parse multi-line constructors or constructor arguments that are earlier types; fixed (PCWL_gen_equalities.py changes 1 to 4).
* CurrentCompactCallerTypesV1: 10 of 10 settled. PRVEq_CurrentCompactCallerTypesV1_w2.lean (PCWL_L006, exit 0). Fresh = PCVJ_E002 (extended Aeneas, ON, frozen); parametric structures and Array/Vec/Slice/Option fields now handled.
* CurrentClaimSumModel: 6 of 10 settled (WideExact, Challenges, SemanticTranscript, Verified, Error as isomorphisms with a crate-path name map, PCWL_L014; WideExact.ZERO fresh = gate, PCWL_L015). Open: prepared_claim_sum, _loop, _loop.body (CANNOT_EXTRACT) and prepared_claim_dot.closure.
* AdapterRwModel: 7 of 12 settled. EQUALITY_PROVED: readonly_buffer_meta_ok, require_readonly_buffer (PCWL_L009), require_zero (PCWL_L027). CONDITIONAL_ON_BINDING: readonly_meta_ok, require_readonly_account (PCWL_L012; bound to ops.op36, the Pubkey equality external). GATE_ONLY_HELPER cleared through parent: require_zero_loop, require_zero_loop.body. Open: require_distinct_accounts and its three loop items (CANNOT_EXTRACT), authenticate_invariant_release_registry (Ops instance not built; see PCWL_REMAINING.json).
* S1ClaimBorrowedAbiNativeV1 (11) and S1ClaimOwnedNestedModelV1 (10): 0 settled. The owned_* names have no frozen function; their frozen counterpart is verifier::prepared_claim, which cannot be extracted.

## Extraction evidence
E001 original Aeneas on require_zero, require_readonly_*, require_distinct_accounts: partial output; require_distinct_accounts fails ("Returns inside of nested loops are not supported yet"). E002 extended Aeneas on the saved LLBC: exit 2 without message. E003 and E004 extended full runs: uncaught Not_found in InterpReduceCollapse.collapse_ctx_following_sequence (loop with return). E005: controller input assertion (unmatched opacity entry), spec fixed. E006 original Aeneas on verifier::prepared_claim with 9 opaque callees: the same nested-loop return error. The loop-return class is retired for these tools.

## Next deliverables
See PCWL_REMAINING.json: Ext record for authenticate_invariant_release_registry (28 externals of NMX_registry) with bindings against the compiled numbering; Aeneas support for returns in nested loops, then extraction of require_distinct_accounts and prepared_claim.

Target not yet established
