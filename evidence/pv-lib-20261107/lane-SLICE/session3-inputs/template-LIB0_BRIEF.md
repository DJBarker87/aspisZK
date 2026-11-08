# LIB: shared RSL instantiation job (Codex brief, ready to paste)

You are the single shared instantiation worker (LIB) of the Aspis R1 spend-path soundness programme, Stream A, under lead ruling (bp)(2)(c) of docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md. Read rulings (bm), (bn), (bo) and (bp) of that file, the "Security and proof discipline" section of /Users/dominic/ZK/AGENTS.md, and evidence/lib-map-20261107/LIB0_MAP.md, with its JSON LIB0_MAP.json. The map is your field list. Do not rediscover it. If a map entry is wrong, record why in LIB_FINDINGS.md and continue.

Target not yet established. Your work counts as progress only through fully instantiated library fields consumed by a row candidate or a top interface field ((bp)(3)).

## 1. Goal

Build concrete instances `L⋆ : RSL.PoolLib`, `D⋆ : RSL.DeployedIds`, `V0⋆ : RSL.TX2_241.V2Lib`, `VL⋆ : RSL.VLib`, `P⋆ : RSL.PreparedNew VL⋆` and `C⋆ : RSL.TX1_345.S1Lib VL⋆` of the FROZEN RSL rev2 structures (be66076856e, evidence/rowspec-lead-20261107). Each field is proved from the CLOSED ledger25 root that LIB0_MAP.json names for it (evidence/ledger25-20261111/NMQ_LEDGER.json.xz). The principal row folds are already parametric in these structures; your instances let them close by application.

## 2. Binding rules

1. **Specs are frozen.** You never edit RSL_*, TAS_* or any merged job module. A spec change needs a demonstrable error against frozen source 4bb3b3f51e1, written up in LIB_FINDINGS.md; the lead applies it.
2. **Exact fields.** Each field equals the model in its CLOSED root at SAME arguments. A `Child.dom` is the child's ledger caller clause, verbatim (RSL_LEDGER_CLAUSES.json; prose clauses get a Lean transcription with the clause id). Weakening a domain or law, or setting a domain to `False`, is a gate finding.
3. **Graph-of-model laws.** Every `Child.law` and every Spec-valued PoolLib field is the graph of the root's deterministic model at (args, env), plus only the abort prefixes named in the RSL comment. It is never the image of a native Cut/Windows relation.
   - Each such field also exports a `Returns` evaluator in the NND_Returned / AMN_ReturnedPath shape.
   - Each emitted-copy carrier bridge is a separate lemma.
4. **Hypotheses.** No sorry, no axiom, no `opaque` stand-in, no free Ops dictionary, and no child-success or allocator-success premise. Do not add a new trust row.
5. **Resources.**
   - Use the coherent host workspace with the ledger25 export and NLX_COMBINED_IMPORT. Every scope is capped at MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0. The whole host may run at most six concurrent scopes ((bm)(4)(e)), and each scope needs its admission JSON.
   - Compile one file at a time with `lake env lean`. Before any large term, inspect its shape (AGENTS.md formal workflow).
   - After a failed attempt, change the shape before retrying. After two failures of the same shape class, stop that shape and record why.
   - 0 Kani and 0 extraction are authorised.
6. **Audit and reporting.** Each module audits only its own new roots (`#print axioms`: standard axioms only). Record target, exit status, wall time, peak RSS, swap and revision for each scope in LIB_VALIDATION.json.
7. **Git.**
   - Work in a sparse worktree on branch codex/cx-lib-inst-<date>, writing under evidence/lib-inst-<date>/ with the prefix LIB_.
   - Commit with plain messages and no AI trailer.
   - Do not push. Never touch other worktrees or index.lock.

## 3. Deliverables: one small module per field group, in this order

Each module defines its fields and proves each from the named root. Rows and roots are those in LIB0_MAP.json; read each root's full statement before installing it.

| # | Module | Fields / content | Supplying CLOSED rows | Reuse |
|---|---|---|---|---|
| 0 | LIB_Carriers | Byte/array/Result/Obs carrier maps (`ok`→ret, `fail`→abort with prefix, `div`→diverge); `Spec.graph`, `Child.ofFn`; Returns glue; emitted-copy bridges | n/a | NMS_R2N_Interpreted, NNC_ByteCarriers, NMS_R2N_RSLScalars, AMN_ReturnedPath, NND_Returned, PrefixAdapter.fromOld |
| 1 | LIB_Env | Instantiate the roots' `hashv`/`Digest32` from `Env.sha256` with `Event.digest`; PDA reply; clock | TX1:327/TX2:210 (SolanaDigest) | NNC_RuntimeOracle, NNC_DigestTrace, NNE_Clock, NND_RuntimePartial |
| 2 | LIB_Deployed | `D⋆.pool`, `D⋆.registry` | TX2:220, TX2:225 | none |
| 3 | LIB_ErrorDebug | `V2Lib.VErr/debug`, `VLib.VErr/debugV` (one carrier) | TX2:211, TX1:NGB001 | NGL_ErrorModel, NMS_R2ErrorSource |
| 4 | LIB_Root0 | `V2Lib.Root0` := NLP_InputDomain.Root0 on bytes; R0 byte link | n/a (headline predicate) | NNC WeakR0Rep, NNC_ByteCarriers |
| 5 | LIB_Transcribed | (bm)(2)(c) lemmas: CLOSED root implies the RSL transcription on the call domain, for readonly*, verifierCheckpoint (unrestricted, with clone arm), requireDistinct (3/7), requireZero, data/data_len/key, snapshot, is_active_at, flags, Box wrappers, admitted, decode_digest_canonical, error/mapVErr, observer, mark (arbitrary obs; F8) | see the transcription table in the map | NMV snapshot laws, NMS_R2GetterLink.full, NND L117 |
| 6 | LIB_PoolCarriers | PoolLib Request/Statement/Afterstate; Master/Checkpoint/Registry/Entry carrier maps | n/a | none |
| 7 | LIB_PoolRegistry | validatePolicy, decodeRegistryV1/V2, decodeEntryV1/V2 | TX2:151, 203, 204, 201, 202 | NND_RegistryLibrary (then tie each to its CLOSED root, not only to the AdapterRw op) |
| 8 | LIB_PoolAccounts | decodeMaster, decodeCheckpoint | TX2:153, TX2:152 (NJY_Roots) | none |
| 9 | LIB_PoolDecoders | decodeRequest, reqProfile/Release/PoolProgram, reqNullifier (eight-word array → B32), outputLane | TX2:163, 158, 156 | NMS_R2DecoderImage, NMS_R2NullifierCarrier, NMS_R2LaneModel, NMS_R2Gated242 |
| 10 | LIB_PoolEffects | scanProof, reconstruct, encodeStatement (array by value, no alloc arm), emitResult (returnData event) | TX2:226, 224, 165, 219 | NMS_R2PoolSites |
| 11 | LIB_PoolLib | Bundles `L⋆`, `D⋆`; `NND_PoolValues.Values L⋆` | n/a | none |
| 12 | LIB_Tx2Auth | Canonical `tx2auth` from NMN_064.root (TAS name `NMN_064.rslRefines`: `Refines064 V0⋆ I.f064 V0⋆.Root0 V0⋆.tx2auth` once `I.f064` is fixed); weak `NNC_ObservedLaw.w` registered as `TAS.lib V0⋆ (fun _ _ => True) w` | TX2:064 | NNC_ObservedLaw, NNC_G1a |
| 13 | LIB_V2Lib | Bundles `V0⋆` | n/a | none |
| 14 | LIB_VCarriers | 20 VLib carriers (QM31 := canonical subtype; Prefix keeps its source bytes), qDec/pDec, six error constructors, codecToV (candidate.rs:22), reads eta/at28/c1Root/viewSemantic/origChallenges, zeroE29 | n/a | NMT_R2_PublicLibrary (Public carrier) |
| 15 | LIB_VField | qadd, qmul (certificate theorems NEB_QMCalls.add/multiply; F5), maskValue | TX1:024, 029, 076 | none |
| 16 | LIB_VRecords | validatedRecord, decodeK29, payload, state | TX1:141, 147, 139, 146 | none |
| 17 | LIB_VParse | parsePrefix, semanticBytesDom, publicTranscript, begin | TX1:138, 131, 150 | NMP_ parse/public/begin adapters |
| 18 | LIB_VSemantic | semanticRounds, circle, claims (F1), terminalQm31, publicDom, finishInputDom (F7: clause-by-clause table) | TX1:134, 142, 129, 256; NLS/NJW/NKN clauses | NMT_345PublicDomain |
| 19 | LIB_VPrepare | filled (F1), expandSemantic, expandValues, wideView | TX1:064, 098, 099, 095 | none |
| 20 | LIB_VTx1A | parseShape, canonicalScan, accNew (F1), weightsNew (F1), finish | TX1:086, 084, 174, 176, 175 | none |
| 21 | LIB_VTx1B | batchMerkle (dom NLO-bf 64-67), geometry, queryLoop, checkpoint (dom DriverEstablishedDomain; F6) | TX1:081, 181, 088, 186 | none |
| 22 | LIB_VLib | Bundles `VL⋆`; per-field Returns evaluators | n/a | none |
| 23 | LIB_Prepared | `P⋆` (complete 179 law; F2/F3) | TX1:179 | NMP_ source call |
| 24 | LIB_S1 | `C⋆`: retarget NMT_R2_ReachLibrary.library from `NMT_R2.TX1_345` to `RSL.TX1_345.S1Lib`; decodeReachesAlloc association (F4) | TX1:332, 276, 278∘267, 268 | NMT_R2_ConcreteS1, NMT_R2_Reach* |
| 25 | LIB_Instances | Final bundle; `example : <job root type> = <TAS field type> := rfl` checks; axioms | n/a | none |

**Order.**
- Modules 0-5 come first.
- The TX2 lane follows, in order: 6, 7 (needed by 234), 8 (233), 9-10 (242/241), 11-13.
- The TX1 lane is: 14, 15-17, 18 (136/137), 19 and 23 (087), 20-22 (094), 24 (345).
- The two lanes may run concurrently within the six-scope host count.
- Module 25 comes last.

## 4. Fields gated by lead rulings: build the rest first

- **F1.** `filled`, `accNew`, `weightsNew`, `claims` and `tx2auth` carry fallible try_reserve Err arms, and the Env has no reply channel for them. Install each one as an explicit module parameter `(law : …)` together with a lemma stating the root's relational law. Do not fix the reservation to success, and do not claim a Returns evaluator for these fields. Wait for the lead's Env ruling.
- **F2.** `P⋆.dom` cannot be discharged at TX1:087 until the lead rules on the R4 clause. Build `P⋆.law` (F3) anyway.
- **F3, F4, F6, F7, F8.** These are missing child lemmas, which you prove here from the same emitted bodies the CLOSED roots use. If one turns out to be unprovable, write the counterexample or obstruction in LIB_FINDINGS.md and stop that field.

## 5. How the principals consume the instances

- **TX1 principal** (136 → 137 → 087 → 094 → 328 → 345, then 344/333/330):
  - Each fold is already parametric in `(VL, P, C)`. A candidate is `fold VL⋆ P⋆ C⋆ <child roots>`.
  - Field-fact parameters that the folds took, such as `NMT_R2_345.ValidatedPublic`, `NMT_R2_345.Allocation` and the 136 child laws, are discharged by LIB theorems with matching statements.
  - `VL⋆.Public` is the codomain of `C⋆.semanticPublic`.
- **TX2 principal** (217, 234 → 233 → 242 → 241, then 240/221/213):
  - The folds are parametric in `(L, D, V)`. Canonical candidates use `V0⋆`.
  - The weak G1b/G2 path uses `TAS.lib V0⋆ (fun _ _ => True) NNC_ObservedLaw.w`.
  - Intermediate hypotheses such as NMS `ScannerExtent`, the Pool effect laws and the getter laws become LIB theorems at `L⋆`.
- **Integration job:** `NND_A1/A2` (AMN R2 route) consume your Returns evaluators via `NND_PoolValues.Values L⋆`, `NND_Tx2Values.Values V0⋆` and `NND_Tx1ReturnedValues`. A1 stays blocked by F1 until the lead rules.
- **Coherence:** every principal must name the SAME `L⋆ D⋆ V0⋆ VL⋆ P⋆ C⋆`. LIB_Instances checks each consumer's statement against the TAS field by `rfl`.

## 6. Budget and stop

Plan for about 140 focused Lean scopes (stop for review at 200), plus one combined import and one own-root audit at the end. Before the first scope, record which module is expected to take the time. At 80% of budget, review member by member.

## 7. Handoff

Write LIB_HANDOFF.md, LIB_REMAINING.md, LIB_FINDINGS.md, LIB_VALIDATION.json and LIB_CLOSED.json. For each field, record:
- the defining term;
- the supplying root;
- the bridge lemmas;
- the Returns evaluator;
- what is still a parameter, and why.

Use the AGENTS.md section 8 format, and say "target not yet established".
