# PCXC_NOFROZEN_REACH: do the 8 gate-only definitions reach the headline or the closed rows?

Target not yet established. Constant-level reachability only; this does not show that anything is semantically used (limits at the end).

All 8 definitions that have no counterpart in the frozen Rust source are reachable from the headline theorem AspisR1.TAS_FinalB.deployed_splitB, and every one of them is also reachable from at least one closed-row root. None is unreachable.

| definition | from deployed_splitB | closed-row roots | rows | shortest witness from deployed_splitB (hops, theorem nodes) |
|---|---|---|---|---|
| `AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value` | yes | 27 | 31 | 9 hops, 5 theorem nodes |
| `AspisR72Sampler.field.r23_product_u32_bounded` | yes | 40 | 29 | 11 hops, 3 theorem nodes |
| `AspisR72Sampler.field.r24_canonical_mul` | yes | 35 | 27 | 10 hops, 3 theorem nodes |
| `AspisR72Sampler.field.r24_canonical_mul.PP` | yes | 35 | 27 | 11 hops, 3 theorem nodes |
| `AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call` | yes | 35 | 27 | 11 hops, 3 theorem nodes |
| `AspisR72Sampler.field.r24_canonical_mul.closure` | yes | 35 | 27 | 12 hops, 3 theorem nodes |
| `AspisR1ClaimsUnrolledParent.candidate_claims.claims` | yes | 23 | 25 | 6 hops, 3 theorem nodes |
| `NJT_ClaimsRef.r1_semantic.NJT_claims_ref` | yes | 12 | 12 | 9 hops, 1 theorem nodes |

## What each one is and where it is reached

### `AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value`
Module AspisR1DecodeKFullV10.Funs, provenance status OPEN.

From deployed_splitB (9 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_Rest.assemble[thm] -> AspisR1.NNH8_RestClaims.produce[thm] -> AspisR1.FJu_GlobalOwners.complete[thm] -> AspisR1.FIr_PhysicalInitial.on_run[thm] -> AspisS1ExtractedRoundChildren.decodeMain[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (8 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.NHS_NFWObligation.source[thm] -> AspisR1.NHS_PrepareFields.installed[thm] -> AspisS1ExtractedRoundChildren.children[def] -> AspisS1ExtractedRoundChildren.decodeMain[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value[def]

From closed-row root `AspisR1.NKA_ClaimsRoot.claims` (7 hops): AspisR1.NKA_ClaimsRoot.claims[thm] -> AspisR1.NKA_ClaimsEffects.parsed[thm] -> AspisR1.NKA_ClaimsModel.parsed[thm] -> AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body[def] -> AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value[def]

Closed-row roots reaching it: 27; rows: TX1:087, TX1:094, TX1:098, TX1:129, TX1:133, TX1:134, TX1:136, TX1:137, TX1:147, TX1:151, TX1:152, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:193, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `AspisR72Sampler.field.r23_product_u32_bounded`
Module AspisR72Sampler.Funs, provenance status NO_FROZEN_COUNTERPART.

From deployed_splitB (11 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_Rest.assemble[thm] -> AspisR1.NNH8_RestSetup.produce[thm] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.square[def] -> AspisR72Sampler.field.CM31.square[def] -> AspisR72Sampler.field.r23_product_u32_bounded[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (10 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.F3V_Install.configuration[def] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.square[def] -> AspisR72Sampler.field.CM31.square[def] -> AspisR72Sampler.field.r23_product_u32_bounded[def]

Closed-row roots reaching it: 40; rows: TX1:027, TX1:034, TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `AspisR72Sampler.field.r24_canonical_mul`
Module AspisR72Sampler.Funs, provenance status NO_FROZEN_COUNTERPART.

From deployed_splitB (10 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_Rest.assemble[thm] -> AspisR1.NNH8_RestSetup.produce[thm] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (9 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.F3V_Install.configuration[def] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def]

Closed-row roots reaching it: 35; rows: TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `AspisR72Sampler.field.r24_canonical_mul.PP`
Module AspisR72Sampler.Funs, provenance status NO_FROZEN_COUNTERPART.

From deployed_splitB (11 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_Rest.assemble[thm] -> AspisR1.NNH8_RestSetup.produce[thm] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def] -> AspisR72Sampler.field.r24_canonical_mul.PP[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (10 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.F3V_Install.configuration[def] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def] -> AspisR72Sampler.field.r24_canonical_mul.PP[def]

Closed-row roots reaching it: 35; rows: TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call`
Module AspisR72Sampler.Funs, provenance status NO_FROZEN_COUNTERPART.

From deployed_splitB (11 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_Rest.assemble[thm] -> AspisR1.NNH8_RestSetup.produce[thm] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def] -> AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (10 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.F3V_Install.configuration[def] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def] -> AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call[def]

Closed-row roots reaching it: 35; rows: TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `AspisR72Sampler.field.r24_canonical_mul.closure`
Module AspisR72Sampler.Types, provenance status OPEN.

From deployed_splitB (12 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_Rest.assemble[thm] -> AspisR1.NNH8_RestSetup.produce[thm] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def] -> AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call[def] -> AspisR72Sampler.field.r24_canonical_mul.closure[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (11 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.F3V_Install.configuration[def] -> AspisR1.F3M_CircleSource.install[def] -> AspisR1.F3M_CircleSource.source[def] -> AspisR1CircleSampleWrapper.sampler.circle_sample[def] -> circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_ood_circle_point_from_parameter[def] -> AspisR72Sampler.circle.secure_circle_point_from_parameter[def] -> AspisR72Sampler.field.QM31.mul[def] -> AspisR72Sampler.field.r24_canonical_mul[def] -> AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call[def] -> AspisR72Sampler.field.r24_canonical_mul.closure[def]

Closed-row roots reaching it: 35; rows: TX1:087, TX1:094, TX1:136, TX1:137, TX1:142, TX1:156, TX1:168, TX1:169, TX1:170, TX1:186, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX1:NGB002, TX1:NGB004, TX1:NGB006, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `AspisR1ClaimsUnrolledParent.candidate_claims.claims`
Module ClaimsUnrolledParentSource, provenance status OPEN.

From deployed_splitB (6 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> AspisR1.NNH8_HeadlineB.headlineB[def] -> AspisR1.NNH8_HeadlineB.headlineB._proof_1[thm] -> AspisR1.NNH_OutcomeRecAccepted.accepted[thm] -> AspisR1.IDa_Deployed.boundaries[def] -> AspisR1.ClaimsUnrolledFinish.claims[def] -> AspisR1ClaimsUnrolledParent.candidate_claims.claims[def]

From closed-row root `AspisR1.NHS_CheckpointPacket.source` (5 hops): AspisR1.NHS_CheckpointPacket.source[thm] -> AspisR1.NHS_NFWObligation.source[thm] -> AspisR1.NHS_PrepareFields.installed[thm] -> AspisR1.ClaimsUnrolledFinish.install[def] -> AspisR1.ClaimsUnrolledFinish.claims[def] -> AspisR1ClaimsUnrolledParent.candidate_claims.claims[def]

From closed-row root `AspisR1.NKA_ClaimsRoot.claims` (2 hops): AspisR1.NKA_ClaimsRoot.claims[thm] -> AspisR1.ClaimsUnrolledFinish.claims[def] -> AspisR1ClaimsUnrolledParent.candidate_claims.claims[def]

Closed-row roots reaching it: 23; rows: TX1:087, TX1:094, TX1:129, TX1:136, TX1:137, TX1:168, TX1:169, TX1:170, TX1:179, TX1:186, TX1:193, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:151, TX2:197, TX2:198, TX2:199, TX2:200, TX2:213, TX2:220, TX2:221, TX2:225.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

### `NJT_ClaimsRef.r1_semantic.NJT_claims_ref`
Module NJT_ClaimsRef_Funs, provenance status OPEN.

From deployed_splitB (9 hops): AspisR1.TAS_FinalB.deployed_splitB[thm] -> NNH_Libraries.VL[def] -> LIB_Instances.VL[def] -> LIB_VLib.library[def] -> LIB_VSemantic.claims[def] -> LIB_VClaims.claims[def] -> LIB_VClaims.eval[def] -> LIB_VClaims.value[def] -> LIB_VClaims.parent[def] -> NJT_ClaimsRef.r1_semantic.NJT_claims_ref[def]

From closed-row root `AspisR1.NKA_ClaimsRoot.claims` (2 hops): AspisR1.NKA_ClaimsRoot.claims[thm] -> AspisR1.NKA_ClaimsEffects.reference[def] -> NJT_ClaimsRef.r1_semantic.NJT_claims_ref[def]

Closed-row roots reaching it: 12; rows: TX1:087, TX1:094, TX1:129, TX1:136, TX1:137, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:213, TX2:221.

Root names: see PCXC_NOFROZEN_REACH.json (roots_reaching).

## What this check cannot see

* Constant-level reachability is not semantic use: a definition that occurs in the cone may sit only inside a theorem statement, an unused branch, a dead binding, a type-level mention or a proof term that never computes with it. The check does not decide which.
* It does not decide whether the Rust function this definition models runs in the deployed ELF; for gate-only helpers there is no frozen function to compare with.
* Only 2 of the 1099 ledger roots were walked on the .olean objects (NHS_CheckpointPacket.source and NKA_ClaimsRoot.claims, which between them cover all 8 definitions apart from the splitB root); the other root attributions are list-level (pinned lists from ledger29, not re-derived on the ledger30 objects).
* Pinned lists for ledger roots come from ledger29 NNM_raw; ledger30 re-audited only 4 other roots (NNN_raw), so a drift of a root list between ledger29 and ledger30 is not excluded; the walker runs on the ledger30 gate (PCXC_L007) agree with the lists for the two walked roots.

Method and files: PCXC_NOFROZEN_REACH.json (full data), PCXC_REACH_LISTS.json (list level), PCXC_L006 and PCXC_L007 (walker scopes), PCXC_ConeWalk.lean.in (walker source).
