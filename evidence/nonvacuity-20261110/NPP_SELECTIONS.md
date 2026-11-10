# NPP_SELECTIONS: the classical sites the refinement tool did not refine (lead decision)

Stream A, gate row 5, step 3. This note is evidence from NPP_L049 (NPP_ComputableModel.lean,
sha256 08a7deb3…; log NPP_L049/stdout.log). Nothing listed here has been restated or changed. Each
entry says:

- what is chosen or decided;
- whether it is unique;
- what a computable refinement would need;
- what is blocked behind it.

"Blocked" counts the copies of the I.entry / tx1Value / tx2Value / producer cone that stay
noncomputable because they reach the entry.

Target not yet established.

## A. Existential selections (no total-Result shape): decision needed

These are `Classical.choose h` whose predicate has no `r = ok a` conjunct. The tool refines a choice
only when the chosen value is pinned by injectivity of `ok`/`Ok` (section D). These are not.

### A1. `LIBC_ExpandSemanticModel.Row j late` (blocks 14)

- **What is chosen.** A row `r < 27` with `dst r ≤ j < dst r + 5 + payloadSize r`, from
  `(NGV_SemanticPacket.coverage j …).resolve_left late`. That is, the packet whose byte interval
  contains output position `j ≥ 32`.
- **Uniqueness.** The choice is unique if and only if the 27 intervals
  `[dst r, dst r + 5 + payloadSize r)` are pairwise disjoint. No lemma in the cone states that.
  The schedule is meant to be a partition, so the statement is plausibly true. It is a finite fact
  about 27 numerals.
- **Refinement it would allow.** A bounded search: the first `r ∈ List.range 27` satisfying the
  predicate. This is equal to the choice by uniqueness (`Classical.choose_spec` plus disjointness).
- **Decision asked.** Approve proving the disjointness lemma by named per-row facts (AGENTS rule 3,
  not `decide` over the schedule), and use it as the equation. The alternative is to restate `Row`
  as the search.

### A2. `LIBB_AuthCarrier.raw a` (blocks 5)

- **What is chosen.** `if h : ∃ r, NND_Carrier.auth r = a then some (Classical.choose h) else none`.
  This is a partial inverse of the carrier map from `AuthenticatedAsq8Accounts` to
  `RSL.Authenticated`.
- **Uniqueness.** Unique when it exists, by `NND_Carrier.auth_injective`, which the module uses in
  `roundtrip`.
- **Why it is not refined.** Two steps are missing: the `if` is on an existential, so a decision
  procedure for `∃ r, auth r = a` is needed; and the value needs a computable inverse.
- **Refinement it would allow.** A hand-written field-wise inverse `inv : RSL.Authenticated → Option Raw`,
  with `auth r = a ↔ inv a = some r`. That lemma decides the existential and pins the choice, and
  the equation follows from it and injectivity.
- **Decision asked.** Approve the hand-written inverse plus its two lemmas as a refinement. The
  definitions themselves are not restated.

### A3. `LIBB_NullifierBytes.digest b` (blocks 16)

This has the same shape as A2, for `LIBB_NullifierBytes.key : Digest → RSL.B32`, which is injective
(`injective`, used in `roundtrip`). The refinement would be the inverse byte decoding, with
`key d = b ↔ inv b = some d`. The decision asked is the same as for A2.

### A4. `NMX_R6_NativeLive242.observation choices program accounts data slot env` (blocks 16)

- **What is chosen.** `Classical.choose (live …)` with
  `live : ∃ o, NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices) program accounts data slot env o`.
  Here `o : RSL.Obs (Result ValidatedAsqa ProgramError)`. `meaning` is
  `NMS_R2N_242Code.body (children devnet) authenticate`, a relational reading of the native 242
  children. Its docstring says "all nondeterminism is the retained std allocation interpretation".
- **Uniqueness.** Not established. `o` is unique exactly when `meaning … ·` is functional for fixed
  `choices`. That depends on whether the std-allocation interpretation fixed by `choices` resolves
  every branch.
- **Refinement it would allow.** If it is functional: a functionality lemma, plus a computable
  evaluator of the 242 children body as the refinement. If it is not functional: there is no
  equation; the observation is a genuine selection and would need a restatement, for example
  `choices` carrying the observation.
- **Decision asked.** Which of these two routes to take. NMX_R9_Live241.observation (the same shape
  for 241, "a source selection") was not reached, because it sits behind A4. It is expected to need
  the same decision.

## B. Decidability sites that no structural instance can refine as stated: decision needed

### B1. `AspisR1.NNG_TypedEvents.select` (blocks 17)

- **The site.** `if h : A = Args then effects (cast h args) else []`. The branch is on an equality of
  *types* (`A Args : Type`), decided classically.
- **Why it cannot be refined.** Type equality has no decision procedure in Lean, so no refinement
  exists for this definition as written.
- **Decision asked.** A restatement, for example decoding by a value-level tag or a typed-event code
  instead of `A = Args`. That is a model change and needs your review; I have not made it.

### B2. `NJE_WellFrozen.emitted` (blocks 46)

- **The site.** The classical instance `Classical.propDecidable reject` in
  `let reject ← …; if reject then ok false else …`, where the source's `reject` is a `Bool`.
- **Why it was not refined.** The logged class is `Decidable reject`. Its carrier is either a Prop
  coercion of the Bool or a Prop binder. Neither instance search nor the recursive procedure found
  an instance.
- **Diagnosis.** This is probably mechanical (`Bool` equality is decidable), but it needs one
  inspection of the elaborated term. I did not spend a scope on it.
- **Decision asked.** None, unless the elaborated `reject` turns out to be a genuine `Prop`; in that
  case the same question as B1 arises.

## C. Decidability sites that need a hand-written decision procedure (no decision needed; work items)

### C1. `LIB_VDecode.decodeK29` (blocks 79, the largest)

- **The predicate.** `Domain r n := NGO_CallerDomains.Call r.row.val 29 n ∧ r.framed.val.length = …`.
  `Call` is an inductive Prop with three constructors:
  - `initial : Call 14 1 0`;
  - `round : 15 ≤ row → row ≤ 24 → Call row 28 0`;
  - `claims : p < 3 → Call 25 29 (p*29)`.
- **The work.** A `Decidable (Call r a n)` instance, with its characterization lemma proved by
  `cases`. The existing Subsingleton equation then applies.

### C2. `LIB_VTerminal.model` (blocks 4)

- **The predicate.** `Domain a := LIB_VPublicDomain.publicDom a.1`, which is
  `NKR_DigestChildren.Domain … ∧ asset_id < 2147483647`. The first conjunct is a *structure* Prop:
  - `dc` on six digests;
  - `∀ d, p.recipient = some d → dc d`;
  - `∀ d ∈ list, dc d`.
- **The work.** A `Decidable` instance via the field conjunction (`decidable_of_iff` with the
  structure's constructor and projections), provided `dc` is decidable.

## D. Refined and proved equal (for reference; no decision)

Every total-Result choice in the cone was refined through the tool extension. Each is now
`okOf r h'` or `okOkOf r h'`, built over the *copies* of its dependencies, with the equation
`okOf_eq ∘ choose_congr` and standard axioms. The refined leaves are:

- NJM_CircleJoin.point;
- LIB_VArithmetic.qadd and qmul (subtype value, with the auxiliary proofs transported);
- LIB_VMask.maskValue;
- LIB_VRecords.validatedRecord and payload;
- LIBB_ResultTotal.value;
- NJQ_ChildTotal.identity, policy and master;
- LIB_VClaims.parent (`ok (Ok _)` shape).

## E. Tool limitations (no decision; listed for completeness)

- **`LIB_VClaims.value._proof_2` (blocks 5).** A proof whose type contains another proof
  (`value._proof_1 p row`) applied to a variable typed over the refined `parent`. Transport along a
  single motive cannot type it. A fix needs simultaneous transport of the inner proof.
- **`NKE_CommonEval.source`.** Its copy by substitution exceeded the kernel's memory. It was caught
  and blocked, and no retry was made (AGENTS rule 5). Its type mentions only id-dependent or
  theorem constants.
- **16 copies with code but no `npp_eq`.**
  - The D/registry chain is id-dependent: LIB_Instances.D, NNH_Libraries.D,
    LIBB_PoolLib.deployed, NMX_R5_Request242.D, NMX_R3/R4/R9 authentication and the
    NMS_R2N_Native242Children pieces. These need the stage-B `nov_eq` run (NPP_SdkNovTool pattern),
    which has not been run for this cone.
  - Five NKE_CommonCodec/NKE_CommonProgram definitions carry proofs that mention two placeholder
    groups. The copies are valid, but no equation is claimed for them.

Target not yet established.
