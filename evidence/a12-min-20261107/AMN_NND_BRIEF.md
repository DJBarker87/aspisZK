# NND_ brief, revision 2: minimal A1/A2 (paste as the Codex prompt)

You are resuming job NND_ (A1/A2 model bridge) on branch codex/cx-model-bridge2-20261107, based on `research` at or after the AMN_ commit. Work under evidence/model-bridge2-20261107/ with prefix NND2_. Read first, in order: evidence/a12-min-20261107/AMN_REPORT.md, AMN_Minimal.lean, AMN_ReturnedPath.lean; then evidence/model-bridge-20261111/NND_HANDOFF.md and NND_REMAINING.md; then evidence/phys-adapter-20261111/NNE_AcceptanceSig.lean and NNE_Stage1Error.lean. AGENTS.md binds. Target not yet established.

## 1. The exact target (this supersedes NND_AMENDMENT's "Ok AND Err, complete Result, fresh emissions")

Inhabit `RSL.TAS.NND_A1 (NNE_AcceptanceSig.physical S d) VL P C` and `RSL.TAS.NND_A2 (NNE_AcceptanceSig.physical S d) L D V0` at the canonical libraries. At that Sig these fields are exactly `RSL.AMN.A1min` / `A2min` (AMN `ofNND_*`/`toNND_*`):

- **A2 (Ok only, selected occurrence only):** for `a = child2 d.err (d.e2 c) (d.program c) (d.data2 c) (S.env2 c).clock`, if a `TX2_241.Ref L D V0 a env o` observation returns `.ok ()` (EnvRep, Exhibited), then `d.native2 (S.model2 c) (d.program c) ((d.e2 c).second secondSizes) (d.data2 c) (d.slot c) = ok (.Ok ())`.
- **A1 (all arguments):** if a `TX1_345.Ref VL P C a env o` observation returns `.ok (nativeBytes saved)`, then model1 returns `ok (.Ok saved)`. If it returns `.error _`, then model1 returns `ok (.Err pe)` for SOME `pe`.

**Not required, so do not prove these:**
- A2's Err or abort direction (native2 is never read by game (d); see AMN_REPORT 1.2).
- Error payload equality, log/format strings, event chronology, 064 End/stop arms, digest totality.
- Any fresh-emission extraction or replay. A1/A2 compare the frozen-source RSL reference with the AdapterRw model; emission provenance belongs to the row jobs and lead note (bk).
- Dictionary-wide equality between `NND_RegistryOps.install` and `DrvC_Installation.sdk c`. Only pointwise slot facts at the arguments reached on the paths above are needed.

`NND_Missing.instance` must still be a total definition, because Exhibited is a substitution of `missing` proved by rfl. Its laws are needed pointwise only.

## 2. Route (R2, the NND_Returned shape)

For each parent, use an RSL evaluator `val` with `NND_Returned.Returns (Ref a) env (val a env)`, then transport the MODEL from the value: `val = .ok v → model Ok v` (TX2); for TX1, also `val = .error _ → model Err`. Assemble with `RSL.AMN.viaReturns2/viaReturns1`, then `toNND_A2/toNND_A1`. Liveness is not needed on this route. Do NOT use the model-side-RowSpec route (`AMN.transfer*`): it needs a liveness lockstep that membership does not give (`AMN.alloc_admits_both`).

First, the leaf audit. `AMN.a1_forces_det` shows that A1/A2 are unprovable if a library leaf law on a returned path admits two Ok values at the same arguments and environment. List every PoolLib Spec field used (scanProof, reconstruct, encodeStatement, emitResult), `V0.tx2auth` (NMN_064 law), every VLib Child/PreparedNew field, and the CLOSED root that instantiates each. Record whether each law is returned-functional. A relational law is a finding to report to the lead. Never weaken it.

## 3. Module order, reuse and estimate

Already discharged (reuse; do not redo):
- RSL-side evaluators with Returns: NND_LaneReturned (217), NND_RegistryEval (234), NND_AuthEval (233), NND_ValidateEval (242), NND_Stage2Eval (241), NND_Stage1RefEval (345).
- The Ok half of NND_RegistryReturned.returned (local Ops).
- L117 historical require_zero = RSL.requireZero (all slices).
- L060 op23/op25–34/op48/49 survive into the deployed sdk.
- L043/L044 scalar and predicate transports; L119–L137 decoder totality and projections; L139–L193 policy prefix, registry predicates, terminal checks and SAME-oracle PDA transport; L086/L089 account/checkpoint laws.
- NND_064ParseTransport (Ok exits); NND_ReservationFinding (shows C06 differs only off the Ok branch).

TX2 (A2) first. This is the critical path for accepted2.
1. NND2_PoolValues: inhabit `NND_PoolValues.Values L` from the CLOSED Pool laws. About 6–10 scopes.
2. NND2_AuthValues: inhabit `NND_Tx2Values.Values V0` (Returns of the NMN_064 law on Dom064). About 4–8.
3. NND2_Ok234: the Ok half of RegistryReturned, plus pointwise agreement of the local install with `sdk c` on the slots reached on the Ok path at EnvRep (PDA through EnvRep). About 8–15.
4. NND2_Ok217: `LaneReturned.value = ok l → ` model lane decoder Ok `l`, with op50/native217 installed in NND_Missing.instance. Reuse the NMM_ root if merged. About 10–20.
5. NND2_Ok233 (AuthEval Ok → model authenticate Ok), then NND2_Ok242 (ValidateEval Ok → model validate_asq8 Ok). About 20–40 together.
6. NND2_Ok064: `auth value = ok ()` on Dom064 → `sdk c` op11 Ok. This includes the C06 Ok-branch alignment: on the Ok path the native reservation is Ok, and the model with `reserved = true` reaches the same result. It also includes op43 = digest hashv under Exhibited + EnvRep. About 10–25.
7. NND2_A2: `Stage2Eval.value = ok () → ` model2 Ok at Sel2; then viaReturns2, toNND_A2. About 6–10.

Subtotal TX2: about 65–130 scopes.

TX1 (A1):
8. NND2_VerifierValues: inhabit `NND_Tx1ReturnedValues.Values VL P` (Returns for TX1_094.Ref, through the 087/137/136 references and each VLib Child law). Build it with the NND_Returned combinators. About 25–45.
9. NND2_Op10: `tx1 value = ok b → ` the model's op10 path returns Ok `b`; `= error → ` Err. Lockstep with the model-side CLOSED roots (many are already stated on `VTop_Stages` ops at the DrvC dictionary). Use AMN_ReturnedPath for the Err-class steps. About 25–50.
10. NND2_Ok345: `Stage1RefEval.value = ok b → ` model1 Ok `b`; `= error → ` model1 Err. Uses L117, L086/L089 and the S1Lib decoder/encoder links. About 15–30.
11. NND2_A1: viaReturns1, toNND_A1. About 3–5.

Subtotal TX1: about 70–130 scopes.

Gate: an own-root raw ax2 audit plus one focused combined import (with NNE_RecordSig, to check that a3/a4/a5 accept the two fields). About 4–6 scopes.

Budget: 160 Lean/link/audit scopes for TX2 plus the gate. Stop and hand off after step 7 if TX1 cannot fit; TX1 can then go to a second job with 140. 0 extraction, 0 Kani. The largest uncertainty is steps 8–9 (verifier chain); report their leaf audit before spending.

## 4. Rules

- Single capped scopes (6G/8G/swap0, Lean -M7000). Compile the smallest changed file first.
- No sorry, axiom, Root0 or hash-injectivity premise, no global Ops-compatibility packet, and no new trust row.
- A failed shape is followed by a changed shape. Never raise a cap or timeout.
- Record target, exit, wall, RSS, swap, revision and `#print axioms` per scope.
- Plain commit messages, no push, no edits to TAS_/NNE_/RSL_ files. If a consumer needs `NotOk1` weakened to `≠ ok (.Ok _)`, report it; do not edit NNE.
- Report RZ-STATE (TAS_TopB) as open. Do not resolve it by stamping allocator state on Err invocations, since that needs an owner ruling.
- End with: claim established (theorem names), assumptions discharged/retained, validation run, remaining blocker. Target not yet established.
