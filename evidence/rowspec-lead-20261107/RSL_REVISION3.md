# RSL Revision 3: the two LIB0_ errors F1 and F2 (ruling (bq))

Target not yet established. This revision changes specifications only. It closes no row, and it does not prove that any frozen function satisfies its RowSpec.

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 is unchanged. The specs are frozen under ruling (bp)(4), and ruling (bq) allows exactly two corrections, both demonstrable errors against that source and both reported by LIB0_ (evidence/lib-map-20261107/LIB0_MAP.md). Nothing else was changed. The trust rows, runtime assumptions, security metric, the other own-input domains and every other Ref are as in Revision 2. LIB0_ F3, F4, F6, F7 and F8 are missing child lemmas, which belong to LIB_. They are not addressed here.

Base: research a1c9c55ad28. Branch: codex/cx-rsl-rev3-20261107.

## 1. F1: the reservation reply in `Env`

**Error.** `heap::filled` and `heap::uninit` (crates/aspis-core/src/r0/heap.rs:5-14) call `try_reserve_exact(..).map_err(|_| Error::Allocation)?`. A failed reservation is therefore a returned `Err(Allocation)`, not an abort. Revision 2's `Env` carried only sha256, pda and clock, so no law could select between the Ok and Err arms. The laws of `VLib.filled`, `accNew`, `weightsNew`, `claims` and `V2Lib.tx2auth` had to be relations admitting both arms at the same arguments and Env. As a result `AMN.a1_forces_det` made A1 unprovable. The Revision 2 header also claimed that the only nondeterminism was the aborting allocation site, which is false for try_reserve sites.

**Fix.** `Env` gets one new field, `reservation : Bool` (`true` = `Ok(())`). Fallible sites read it through `Spec.tryReserve`. The reply is bound to the headline binder `reservation : NP6_StdModel.Reservation` in `TAS.Sig.EnvRep`.

Before (RSL_Base.lean):
```lean
structure Env where
  sha256 : List Bytes → B32
  pda : List Bytes → B32 → Option B32
  clock : Except ProgramError UInt64

def env0 : Env := ⟨fun _ => zero32, fun _ _ => none, .error .unsupportedSysvar⟩
```
After:
```lean
structure Env where
  sha256 : List Bytes → B32
  pda : List Bytes → B32 → Option B32
  clock : Except ProgramError UInt64
  reservation : Bool   -- try_reserve reply, true = Ok(()); docstring states the binding

def Spec.tryReserve : Spec Bool := Spec.env Env.reservation
def Spec.Functional {α} (m : Spec α) : Prop := ∀ env, ∃ o, ∀ o', m env o' ↔ o' = o
def Child.Functional {A B} (c : Child A B) : Prop := ∀ a, c.dom a → Spec.Functional (c.law a)   -- RSL_Verifier

def env0 : Env := ⟨fun _ => zero32, fun _ _ => none, .error .unsupportedSysvar, false⟩
```

Shape of the reply. There is one Bool for every try_reserve occurrence in a transaction. This matches the headline exactly: `NP6_StdModel.calls reservation` returns the same `reservation` at every `reserve` call, and `FIp_Install.configuration … reservation` installs that one binder. A per-occurrence family (LIB0_'s first suggestion) would be finer than the headline it must be bound to, so the binding would have to make it constant anyway. The single reply therefore loses nothing relative to the headline. The headline's single-reply modelling is a pre-existing property of the headline; this revision does not introduce it. The TryReserveError payload is discarded by every frozen caller (`map_err(|_| Error::Allocation)`), so a Bool carries all of the reply that can be observed.

Binding (top-assembly-20261107/TAS_Interfaces.lean, docstring of `Sig.EnvRep` only; the Lean type of `Sig` is unchanged):
```
-  /-- `env` agrees with the ctx runtime oracles (sha256 via `syscall`, PDA, clock = slot). -/
+  /-- `env` agrees with the ctx runtime oracles (sha256 via `syscall`, PDA, clock = slot).
+  RSL Revision 3 (ruling (bq), LIB0_ F1): it also binds the reservation reply to the
+  headline binder, `env.reservation = true ↔ reservation = .Ok ()` ... -/
   EnvRep : Ctx → Env → Prop
```
`EnvRep` is an abstract field that the host defines (NNE_, NNE_RecordSig). The host definition must now include this conjunct. I recorded the binding as a docstring rather than as a new `Sig` field so that the TAS Lean shape, which NNH_ instantiates, stays the same. If the lead wants the binding checked in Lean at the TAS level, the next step is a `Sig` field `env_reservation : ∀ c env, EnvRep c env → env.reservation = …`. That would change NNH_'s G0 target.

Gate requirement (doc comments in RSL_Verifier `VLib.filled/claims/accNew/weightsNew` and RSL_TX2_241 `V2Lib.tx2auth`): each of the five laws must read the reservation through `Env.reservation` and be `Child.Functional` on its domain (`Spec.Functional` on `Dom064` for `tx2auth`). An infallible allocation site (Box::new, Vec growth, to_vec, format!) keeps its (bl)(3) abort arm. Abort arms do not return a value, so they do not affect returned-value determinism (`a1_forces_det`). `Spec.alloc`'s comment no longer lists heap::filled as an abort site.

Teeth (RSL_Base, end of file):
- `Spec.tryReserve_functional`: the reply is read, so at a fixed Env there is exactly one observation. No axioms.
- `Spec.functional_of_reserve`: a law of the heap::filled shape (reserve; Ok on true, Err on false) is `Spec.Functional`. Uses [propext].
- `Spec.not_functional_both`: rejection of the Revision 2 relational shape. A law admitting both Ok and Err at the same Env is not `Functional`. Uses [propext].
- `env0.reservation = false`, so the heap::filled-Err hypotheses (`hfill`) of the TX1:087/094 rejection examples are met by a law that reads the reply. Without this they would be unsatisfiable for a faithful law, and the examples would be vacuous.

## 2. F2: own-input clause (R4) on RowSpec_087

**Error.** The TX1:179 root `NHS_PreparedPacket.source` has the premise `compact_check : check_values compact = ok (Ok ())` on the 464-byte y1 slice, and its ledger domain says "LPt compact464 checked". `P.dom` is copied verbatim from 179. Frozen prepare (candidate.rs:255-264) runs `expand_values`, which does no canonicality check (compact.rs:127-136), and never calls `check_values`. With Domain R1-R3 only, RowSpec_087 was unprovable.

**Fix.** There is a new VLib field `checkValuesDom : Bytes → Prop`, which must be instantiated as the 179 `compact_check` premise verbatim. Domain gains (R4). The clause is recorded as caller clause `RSL3-caller:TX1:094:TX1:087:R4` (RSL_LEDGER_CLAUSES.json, TX1:094, status OPEN) and is discharged in RowSpec_094 by canonical_scan. Its first statement is `compact::check_values(&proof[OFF_Y1..OFF_INACTIVE])?` (candidate.rs:55), and tx1 runs it on the SAME proof before prepare (candidate.rs:275-278).

Before (RSL_TX1_087.lean):
```lean
def Domain (V : VLib) (a : Args V) (obs : Observer) : Prop :=
  a.proof.length = VPROOF_BYTES ∧ obs = none ∧ V.publicDom a.public_
```
After:
```lean
def Domain (V : VLib) (a : Args V) (obs : Observer) : Prop :=
  a.proof.length = VPROOF_BYTES ∧ obs = none ∧ V.publicDom a.public_ ∧
  V.checkValuesDom (slice a.proof OFF_Y1 OFF_INACTIVE)
```
RSL_Verifier, VLib (new field, after `semanticBytesDom`):
```lean
  checkValuesDom : Bytes → Prop   -- TX1:179 compact_check premise, verbatim; (R4) of 087
```
RSL_TX1_094.lean (new; `Ref`, `Domain` and `RowSpec_094` text unchanged):
```lean
def R4Discharge (V : VLib) : Prop :=
  ∀ (proof : Bytes) (env : Env) (ev : List Event),
    V.canonicalScan.law proof env ⟨.ret (.ok ()), ev⟩ →
    V.checkValuesDom (slice proof OFF_Y1 OFF_INACTIVE)

theorem r4_of_scan (V : VLib) (hR4 : R4Discharge V) (a : Args V) (env : Env) (ev : List Event)
    (hs : V.canonicalScan.run a.proof env ⟨.ret (.ok ()), ev⟩) :
    V.checkValuesDom (slice (⟨a.public_, a.proof, V.zeroE29⟩ : TX1_087.Args V).proof OFF_Y1 OFF_INACTIVE)
```
`R4Discharge` is a property of the CLOSED TX1:084 law (NKL_ScanRoot). The instantiation (LIB_) must prove it. It is not a hypothesis of RowSpec_094. (R4) narrows 087 only. 094's own Domain (T1, T2) is unchanged, so nothing propagates to 328 or 345.

Rejection examples: `TX1_087.rejects_wrong_g` is unchanged (it takes `Domain` as a hypothesis). `TX1_094.rejects_constErr` gains one hypothesis, `hy1 : V.checkValuesDom (slice a.proof OFF_Y1 OFF_INACTIVE)`, which is needed to enter the 087 call. Its conclusion is unchanged. New: `TX1_087.domain_needs_R4` (no axioms) shows that (R4) really narrows the domain. `TX1_094.r4_of_scan` uses no axioms.

## 3. Files changed

| File | Change | sha256 |
|---|---|---|
| RSL_Base.lean | header paragraph, `Env.reservation`, `Spec.alloc` comment, `Spec.tryReserve`, `Spec.Functional`, `env0`, three teeth | 4fb94e7d2bd91b434d4a90cf2e6e2f65b599955201e85a842ec879872f5ba20c |
| RSL_Verifier.lean | `Child.Functional`, VLib field `checkValuesDom`, comments on the four F1 fields | e6f9a44884888fe2a7301603caae5ed9ad412afa855032b9c51be3214c9f1946 |
| RSL_TX1_087.lean | (R4) in header and `Domain`; `domain_needs_R4` | e17e6561a73c3630596152a9abee43a64cb50739898eae99d58f5ff825fa69c4 |
| RSL_TX1_094.lean | header note, `R4Discharge`, `r4_of_scan`, `hy1` in `rejects_constErr` | 924a56889b3365072a0d28b095aff6318bd4e18ccd6d6a3c61e5b8daae558a81 |
| RSL_TX2_241.lean | `V2Lib.tx2auth` docstring only | d7b9972bce0030ae38566e5d88250189cbc4140b5635c867cef0747000f9e46e |
| RSL_Audit.lean | five `#print axioms` lines for the new teeth | 91929472902786f26e4fb1c34f451d4737e5da913d246bbd46544c7805ec4002 |
| ../top-assembly-20261107/TAS_Interfaces.lean | `Sig.EnvRep` docstring only | 3d7d0c8f079939f7806dfc2d1f1a003387760a238d6a4d5d2dcc910ae81c561b |
| RSL_LEDGER_CLAUSES.json, RSL_INDEX.md | caller clause RSL3-caller:TX1:094:TX1:087:R4; (R4) in the 087 index entry | |
| ../lib-map-20261107/LIB0_MAP.{json,md}, LIB0_fields.py, LIB0_gen.py | F1/F2 marked resolved; new fields `VLib.checkValuesDom`, `Env.reservation` (106 fields); JSON regenerated from ledger25 | |

The other 15 RSL row modules and RSL_Pool are byte-identical to Revision 2.

## 4. Validation

All runs used `lake env lean -o` one file at a time, on Lean v4.31.0, on the development Mac. Peak RSS for any file was 0.73 GB, with 0 swaps.
- RSL_COMPILE_REV3.tsv: all 20 RSL modules, in Revision 2 order, exit 0.
- RSL_AUDIT_OUTPUT_REV3.txt: `RSL_Audit.lean`, exit 0. Every Revision 2 axiom line is unchanged. The new teeth use either no axioms or [propext]. There is no sorry and no axiom declaration (grep).
- RSL_COMPILE_REV3_DEPENDENTS.tsv: TCK_WeakRoot0, TAS_Interfaces, TAS_Top, TFM_TopExact, EVB_EventB, TAS_TopB, AMN_ReturnedPath and AMN_Minimal, staged in .lake/stage and compiled against the rev3 oleans, all exit 0 with no source change other than the EnvRep docstring. RSL_AXIOMS_REV3_DEPENDENTS.txt matches the committed AMN_ and TFM_ axiom outputs line for line. TAS `top`, TASB and EVB use only [propext, Classical.choice, Quot.sound].
- Not compiled: TAS_TopB_NNE (imports NNE_SelectedRoutes, an Aeneas-heavy host module) and top-assembly rev2/TAS_Rev2Support (imports NMV_RslLaws). Neither was on the ruling's list. Both import RSL only through the modules above. If a job constructs an `Env` with a three-field anonymous constructor or builds a `VLib` literal, that job breaks and must add the new component. No module in this checkout does either.

## 5. Impact on live jobs

- **NMX_ (TX2 217/234/233): target unchanged.** RowSpec_217/234/233 and their Refs do not read `Env.reservation`, and their statements are textually identical. The quantifier `∀ env` now ranges over the extended `Env`, which is equivalent because the extra field is never read. Proof code that writes an `Env` literal needs a fourth component.
- **NNG_ (TX1 principal):**
  - 136: RowSpec unchanged. The `claims` instantiation must now read `Env.reservation` and be `Child.Functional`; that is LIB_'s gate obligation.
  - 137: unchanged.
  - 087: **target changed (weakened).** Domain gains (R4). The proof may assume (R4) and use it to discharge `P.dom`'s compact_check clause.
  - 094: **target changed (strengthened at one call).** `RowSpec_094`'s text is unchanged, but its `Ref` calls 087 through `TX1_087.Domain`, which now includes (R4). The proof must discharge (R4) from canonical_scan via `r4_of_scan`, given `R4Discharge V` for the concrete library. The `filled` and `accNew`/`weightsNew` steps are now functional in Env.
  - 328 and 345: statements unchanged textually. They unfold 094's `Ref`, so they inherit the same (R4) discharge through 094, with no new clause of their own.
- **NNH_ (integration):** A1min, A2min, AMN and TAS statements are unchanged and recompile. Rev3 removes the obstruction that `AMN.a1_forces_det` exposed: once the five laws are instantiated as Functional, the TX1 returned path is deterministic at fixed Env, so the A1 Err arm and `NND_Tx1ReturnedValues.returned` / `NND_Tx2Values.auth_ret` are no longer blocked by the spec. RZ-STATE has no change. **G0: target changed in its EnvRep instantiation only.** The host definition of `EnvRep` must also bind `env.reservation` to the headline `reservation`. The `Sig` Lean type is unchanged.
- **LIB_ (concrete library instances): target changed (additions).** LIB_ must:
  1. instantiate `VLib.checkValuesDom` as the 179 compact_check premise;
  2. prove `TX1_094.R4Discharge` from NKL_ScanRoot;
  3. instantiate the five F1 laws reading `Env.reservation` and prove them `Child.Functional` / `Spec.Functional`;
  4. supply `Env.reservation` in `env1`/`env2` consistently with EnvRep.

  `PreparedNew` stays blocked by F3. LIB0_MAP now lists 106 fields, of which 3 are unsupplied or partial (F3, F4, F6).

Target not yet established.
