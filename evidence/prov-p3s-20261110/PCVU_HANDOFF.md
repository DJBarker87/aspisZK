# PCVU_ HANDOFF: phase P3s (tx2 remaining slots)

Target not yet established. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Nothing pushed or merged; no ledger, trust, RSL, contract or shipped source changed; no trust row added. 26 Lean host scopes of 40 and 8 of 8 extraction scopes, one at a time, caps unraised, swap 0 (PCVU_SCOPES.json, PCVU_ATTEMPTS.jsonl, receipts PCVU_Lnnn/, PCVU_Ennn/).

## Difference at a matching configuration
None found.

## Closed (exit 0, standard axioms only; PCVU_STATUS.json)
1. QM31::from_le_bytes (frozen emission PCVU_E001, overflow ON): PCVU_QM31.qm31_16 (PRVEq_QM31_s3, L005) equals decode_k_spec + fromK on every 16-byte window. Off the window the two differ (decode_k_spec has no length check); not claimed.
2. read_checkpoint_semantic_alpha and read_checkpoint_weights (frozen emission PCVU_E002): PCVU_Rd.sem_eq and weights_eq (PRVEq_Rd_s14, L021) equal the deployed readSemanticAlpha / readWeights (then phi), all inputs. The weights equality includes the deferred-writeback versus write-through slice equality. Hand model HM-B intoIterM for the Vec into_iter_mut external (PCVU_HAND_MODELS.json).
3. Composition: PCVU_Tx2Frozen.deployed_tx2_common_t and deployed_tx2_authenticated_t (PRVEq_Tx2Frozen_s2, L022): Ext slots QM31::from_le_bytes, read_checkpoint_semantic_alpha, read_checkpoint_weights are the frozen emission functions; E32 hypothesis discharged by PCVS_Tx2Deployed.e32_deployed; no hypothesis added. Remaining parameters: reserved, query, geo, base, finish.
4. Closure compatibility (L002): the P3 PRVEq objects import together with NNH_HostCtx from the L187 closure; no name clash. NHT_Tx2CommonModel.constants = PCVN_Tx2Deployed.constants (L026), so the P3m text copy is the closure constant.
5. Headline seed (restatement only, L026): query = NJJ_QueryOps.concrete and reserved = (envOf c).reservation. geometry, stageBase and finish equalities by rfl failed (L024, recorded in PRVEq_Headline_s1.lean) and are not claimed; NNH_HostSeed.m0.stageBase has every op = div before stageNNH.

## Plainly: what is only organisation
op5, op6, op9, op10, op19 (and op11) are still instantiated by deployed fields and related to no frozen item. Extraction PCVU_E004, E005, E006 (separate roots), E007 and E008 (five roots, stable --dest-file, byte-identical arguments) all hit the 180 s cap in the Charon/cargo stage; the extraction budget is exhausted. heap::filled is emitted (PCVU_E003) but depends on alloc Vec::try_reserve_exact, which has no entered trust row; the deployed model takes the reservation outcome as the parameter reserved, so a relation would be a hypothesis in place of a deployed field.

## Failed shapes
QM31: s1 and s2 compile errors (missing Option externals, discriminant instance, Canonical open). Rd weights: s5-s13 (rfl across dependent std definitions; fixed by loop_step, body_some, wl_succ lemmas and eliminating a stray have). Headline: s1 stageBase and geometry rfl. Extraction: E004-E008 timeouts.

## Next deliverable
Frozen emissions for op9/op10/op19/op5/op6 with a longer extraction cap or a warmed Charon cache for the stable --dest-file path (PCVU_stable/all.llbc on the host), then a relation per slot; an alloc Vec row decision for heap::filled.
