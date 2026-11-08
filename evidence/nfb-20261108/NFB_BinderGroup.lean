/-
NFB_BinderGroup: corrected binder grouping for the split-B top (TAS/TFM/EVB
stand-in level).

Target not yet established.  Core Lean plus RSL_/TCK_/TAS_/TFM_/EVB_ only.  No
sorry, no axiom declaration, no Root0 hypothesis, no hash-injectivity premise.

Finding (SOUNDNESS-CLAIM-DRAFT-20261108 section 7 item 2).  The docstring of
`RSL.TASB.ExecB` lists `admission1/2` among the oracle-free `Fixed` binders.
Their host types are `RuntimeEntrypointAdmission L e1 w1 3` and
`RuntimeEntrypointAdmission L e2 w2 7`.  Under owner condition (4) `e1` is
`(eval H a.first).2.entry` and `e2` is
`(eval H (a.second i saved post1 final1)).2.entry`, so `e1` depends on H and
`e2` depends on H and on the per-world binders `saved post1`.  Neither
admission can be a `Fixed` binder: at the host the `Fixed` record would have to
contain a proof about an entry that is computed only after `H` and `World` are
chosen.  The only well-typed `Fixed` reading is "admission at every entry the
adversary outputs at every oracle", which is a cross-world restriction on the
adversary.

Corrected grouping (this file; it is what NNH_HostCtx/NNH_LiteralHost already
do at the host):
  * `Fixed` (oracle-free, pair-free): L sdk copy std (host-family
    parameters), allocator := abortIndicator (ruling (bo)), pda, reservation,
    indexError, root, length, prior, words, D, the adversary `a`, Q0, Q1.
    `hashv sha256 p1 syscall` are NOT binders: ruling (bt) instantiates them
    from `H`.  `missing` is NOT a binder: ruling (s) instantiates it from the
    per-world environment (`missingLit`).
  * `World` (per-world data, may depend on H arbitrarily through `wOf`):
    w1 w2 saved post1 post2 p t u actions.
  * Per-world retained trust facts, a predicate `Ret` on the BUILT context:
    `admission1` (at e1, w1), `admission2` (at e2, w2) and `RuntimePersistence`
    (at p).  They enter the actual-run antecedent beside the game frame, as
    `GameFrame' := GameFrame ∧ Ret` and `Game' := Game ∧ Ret`
    (`withRetained`, the literal shape of `NNH_LiteralHost.S_host`).  `build`
    stays total: it takes no admission proof for arbitrary (i, j).

What this file proves.
  1. Every S-dependent TAS/TFM/EVB interface at `S` transfers to
     `withRetained S Ret` unchanged (section 2): the retained conjunct only
     strengthens premises.  No delivered field has to be re-proved.
  2. `ExecB` transfers with literally the same `first`, `second`, `QueriesF`
     and `ERec` (section 3, `exec_same`): the oracle side, the adversary
     binding and the charged event E_rec are unchanged.
  3. Per world (`top_splitB_grouped`): the conclusion is exactly
     `TASB.top_splitB`'s; the only new antecedent is `Ret` at the actual
     context, i.e. the two admissions and persistence AT THE SELECTED ENTRIES,
     which were already hypotheses of `RPx_Deployed.deployed`.
  4. Averaged (`deployed_charge_grouped`): same `r m T each hm budget`, same
     right-hand side; the failure indicator becomes
     `Runs ∧ Ret ∧ ¬OutcomeRec` at the world of H.
  5. Exactly what changes (section 5):
     (a) the averaged failure event gains the conjunct `Ret (ctx H)`;
     (b) under the cross-world reading that the old `Fixed` placement forces
         (`∀ H, Ret (ctx H)`), the new indicator equals the old one pointwise
         (`indicator_eq_of_fixed`), so the corrected averaged theorem implies
         the old-placement one (`grouped_implies_fixed`);
     (c) under the trust reading of the retained rows (the runtime guarantees
         admission/persistence at every executed entry: `Runs → Ret` at each
         H) the indicator is again unchanged (`indicator_eq_of_trust`), so no
         physical run is dropped.  The rows are retained trust, as before; no
         trust row is added, removed or reclassified.
-/
import TAS_TopB
set_option autoImplicit false

namespace RSL.NFB
open RSL.TAS RSL.TFM RSL.EVB RSL.TASB
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)

/-! ## 1. The corrected signature -/

/-- Per-world retained facts enter the game frame and the game.  Host:
`NNH_LiteralHost.S_host` with `Ret := NNH_LiteralHost.retained L`. -/
def withRetained (S : Sig) (Ret : S.Ctx → Prop) : Sig :=
  { S with
    GameFrame := fun c => S.GameFrame c ∧ Ret c
    Game := fun c n1 n2 => S.Game c n1 n2 ∧ Ret c
    mkGame := fun c n1 n2 f r1 r2 => ⟨S.mkGame c n1 n2 f.1 r1 r2, f.2⟩ }

variable {S : Sig} {Ret : S.Ctx → Prop}

theorem gameFrame_iff (c : S.Ctx) :
    (withRetained S Ret).GameFrame c ↔ S.GameFrame c ∧ Ret c := Iff.rfl

theorem game_iff (c : S.Ctx) (n1 : S.First) (n2 : S.Second) :
    (withRetained S Ret).Game c n1 n2 ↔ S.Game c n1 n2 ∧ Ret c := Iff.rfl

/-! ## 2. Interface transfer (premise strengthening only) -/

section Transfer
variable (Ret) {L : PoolLib} {D : DeployedIds} {V0 : V2Lib} {VL : VLib}
  {P : PreparedNew VL} {C : S1Lib VL} {I : Impl L V0 VL}

def tSplit (sp : Split S) : Split (withRetained S Ret) where
  Rest := sp.Rest
  Outcome := sp.Outcome
  concl_iff := sp.concl_iff
  rest := fun c n1 n2 e a g q => sp.rest c n1 n2 e a g.1 q

def tHeadline (hl : Headline S) : Headline (withRetained S Ret) where
  deployed := fun c n1 n2 e a1 a2 g q => hl.deployed c n1 n2 e a1 a2 g.1 q
  numeric := hl.numeric

def tA0 (a0 : A0_Digest S) : A0_Digest (withRetained S Ret) where
  extraction := a0.extraction

def tG1a (g : NNC_G1a S L V0 VL I) : NNC_G1a (withRetained S Ret) L V0 VL I where
  w := g.w
  weak := g.weak
  writeFree := g.writeFree
  okHeader := g.okHeader

def tR0 (r0 : NNC_R0Rep S V0) : NNC_R0Rep (withRetained S Ret) V0 where
  rep := r0.rep

def tA1 (a1 : NND_A1 S VL P C) : NND_A1 (withRetained S Ret) VL P C where
  stage1 := a1.stage1

def tA2 (a2 : NND_A2 S L D V0) : NND_A2 (withRetained S Ret) L D V0 where
  stage2 := a2.stage2

def tA3 (a3 : NNE_A3 S VL P C) : NNE_A3 (withRetained S Ret) VL P C where
  accepted1 := fun c o a1 hx r ok out => a3.accepted1 c o ⟨a1.stage1⟩ hx r ok out

def tA4 (a4 : NNE_A4 S L D V0) : NNE_A4 (withRetained S Ret) L D V0 where
  accepted2 := fun c o a2 hx r ok out => a4.accepted2 c o ⟨a2.stage2⟩ hx r ok out

def tA5 (a5 : NNE_A5 S L V0 VL P C I) : NNE_A5 (withRetained S Ret) L V0 VL P C I where
  recorded := fun c a1 hx h1 g2 rj tr => a5.recorded c ⟨a1.stage1⟩ hx h1 g2 rj tr

def tEntryRep (er : NNE_EntryRep S L V0 VL I) : NNE_EntryRep (withRetained S Ret) L V0 VL I where
  route1 := fun c f t => er.route1 c f.1 t
  route2 := fun c f t => er.route2 c f.1 t

def tRecSig (R : RecSig S) : RecSig (withRetained S Ret) where
  Realizes := R.Realizes
  EventRec := R.EventRec
  SelectsPair := R.SelectsPair

def tRecSelect {R : RecSig S} (rs : RecSelect S R) :
    RecSelect (withRetained S Ret) (tRecSig Ret R) where
  selects := rs.selects

def tHeadlineB {R : RecSig S} (hb : HeadlineB S R) :
    HeadlineB (withRetained S Ret) (tRecSig Ret R) where
  OutcomeRec := hb.OutcomeRec
  outcomeRec := fun c n1 n2 e a1 a2 g q s => hb.outcomeRec c n1 n2 e a1 a2 g.1 q s

def tNMFB {g : NNC_G1a S L V0 VL I} {R : RecSig S} (nmf : NNC_NMFPrimeB S L D V0 VL P C I g R) :
    NNC_NMFPrimeB (withRetained S Ret) L D V0 VL P C I (tG1a Ret g) (tRecSig Ret R) where
  root0_or_rec := fun c hx w ok a1 g e q s => nmf.root0_or_rec c hx w ok a1 g.1 e q s

end Transfer

/-! ## 3. ExecB transfer: oracle side and E_rec unchanged -/

def tExec {R : RecSig S} (X : ExecB S R) : ExecB (withRetained S Ret) (tRecSig Ret R) where
  Fixed := X.Fixed
  World := X.World
  Oracle := X.Oracle
  In1 := X.In1
  In2 := X.In2
  first := X.first
  second := X.second
  build := X.build
  realizes_mk := X.realizes_mk
  exhibited_mk := X.exhibited_mk
  QueriesF := X.QueriesF
  queries_mk := X.queries_mk
  ERec := X.ERec
  eventRec_mk := X.eventRec_mk

/-- The adversary binding (`first`, `second`), the L154 parameter and the
charged event are literally the same objects after regrouping. -/
theorem exec_same {R : RecSig S} (X : ExecB S R) :
    (tExec (Ret := Ret) X).first = X.first ∧ (tExec (Ret := Ret) X).second = X.second ∧
      (tExec (Ret := Ret) X).QueriesF = X.QueriesF ∧ (tExec (Ret := Ret) X).ERec = X.ERec ∧
      (∀ fx w H, ctxB (tExec (Ret := Ret) X) fx w H = ctxB X fx w H) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-- `Runs` at the corrected signature is `Runs` at `S` plus the retained facts. -/
theorem runs_iff {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : Impl L V0 VL) (c : S.Ctx) :
    Runs (withRetained S Ret) I c ↔ Runs S I c ∧ Ret c := by
  constructor
  · intro h
    exact ⟨⟨h.frame.1, h.trace, h.ok1, h.out1, h.ok2, h.out2⟩, h.frame.2⟩
  · intro h
    exact ⟨⟨h.1.frame, h.2⟩, h.1.trace, h.1.ok1, h.1.out1, h.1.ok2, h.1.out2⟩

/-! ## 4. The top at the corrected grouping -/

/-- Per world.  Inputs are the interfaces at `S` (unchanged deliverables);
the only antecedent beyond `TASB.top_splitB`'s is `ret`, the admissions and
persistence at the adversary-selected entries of THIS world. -/
theorem top_splitB_grouped {R : RecSig S} (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) (ret : Ret (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H) :=
  TASB.top_splitB (S := withRetained S Ret) (R := tRecSig Ret R) L D V0 VL P C I
    (tSplit Ret sp) (tHeadline Ret hl) (tA0 Ret a0) nmm nmx nms nmv nmw nmt nmp nmo nmn
    (tG1a Ret g1a) (tRecSelect Ret rs) (tHeadlineB Ret hb) (tNMFB Ret nmfB) (tR0 Ret r0)
    (tA1 Ret a1) (tA2 Ret a2) (tA3 Ret a3) (tA4 Ret a4) (tA5 Ret a5) (tEntryRep Ret er)
    (tExec X) fx w H queries ((runs_iff I _).mpr ⟨run, ret⟩)

/-- The per-world failure event at the corrected grouping. -/
def FailG {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : Impl L V0 VL)
    (hb : HeadlineB S R) (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) : Prop :=
  Runs S I (ctxB X fx w H) ∧ Ret (ctxB X fx w H) ∧
    ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))

/-- The failure event of `TASB.deployed_charge` (old grouping). -/
def FailOld {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : Impl L V0 VL)
    (hb : HeadlineB S R) (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) : Prop :=
  Runs S I (ctxB X fx w H) ∧
    ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))

theorem failG_iff {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : Impl L V0 VL)
    (hb : HeadlineB S R) (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) :
    FailG (Ret := Ret) I hb X fx w H ↔
      (Runs (withRetained S Ret) I (ctxB (tExec (Ret := Ret) X) fx w H) ∧
        ¬ (tHeadlineB Ret hb).OutcomeRec (ctxB (tExec (Ret := Ret) X) fx w H)
          ((withRetained S Ret).model1 (ctxB (tExec (Ret := Ret) X) fx w H))
          ((withRetained S Ret).model2 (ctxB (tExec (Ret := Ret) X) fx w H))) := by
  rw [runs_iff]
  exact ⟨fun ⟨r, t, o⟩ => ⟨⟨r, t⟩, o⟩, fun ⟨⟨r, t⟩, o⟩ => ⟨r, t, o⟩⟩

/-- Averaged over all H.  Same `r m T hm each budget` and the same bound `T`
as `TASB.deployed_charge`; no Realizes, no conditioning, `wOf` and `fx`
arbitrary.  The failure indicator is `FailG`. -/
theorem deployed_charge_grouped {R : RecSig S} (L : PoolLib) (D : DeployedIds) (V0 : V2Lib)
    (VL : VLib) (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed) (wOf : X.Oracle → X.World)
    (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H) (ind (FailG (Ret := Ret) I hb X fx (wOf H) H))) ≤ T := by
  have h := TASB.deployed_charge (S := withRetained S Ret) (R := tRecSig Ret R) L D V0 VL P C I
    (tSplit Ret sp) (tHeadline Ret hl) (tA0 Ret a0) nmm nmx nms nmv nmw nmt nmp nmo nmn
    (tG1a Ret g1a) (tRecSelect Ret rs) (tHeadlineB Ret hb) (tNMFB Ret nmfB) (tR0 Ret r0)
    (tA1 Ret a1) (tA2 Ret a2) (tA3 Ret a3) (tA4 Ret a4) (tA5 Ret a5) (tEntryRep Ret er)
    (tExec X) Ex fx wOf queries r m T hm each budget
  have same : (fun H => max (r H) (ind (FailG (Ret := Ret) I hb X fx (wOf H) H))) =
      (fun H => max (r H)
        (ind (Runs (withRetained S Ret) I (ctxB (tExec (Ret := Ret) X) fx (wOf H) H) ∧
          ¬ (tHeadlineB Ret hb).OutcomeRec (ctxB (tExec (Ret := Ret) X) fx (wOf H) H)
            ((withRetained S Ret).model1 (ctxB (tExec (Ret := Ret) X) fx (wOf H) H))
            ((withRetained S Ret).model2 (ctxB (tExec (Ret := Ret) X) fx (wOf H) H))))) := by
    funext H
    rw [propext (failG_iff I hb X fx (wOf H) H)]
  rw [same]
  exact h

/-! ## 5. Exactly what changes -/

/-- (b) Under the cross-world premise that the old `Fixed` placement forces,
the corrected failure event IS the old one, at every H. -/
theorem indicator_eq_of_fixed {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib}
    (I : Impl L V0 VL) (hb : HeadlineB S R) (X : ExecB S R) (fx : X.Fixed)
    (wOf : X.Oracle → X.World) (fixedRet : ∀ H, Ret (ctxB X fx (wOf H) H)) (H : X.Oracle) :
    ind (FailG (Ret := Ret) I hb X fx (wOf H) H) = ind (FailOld I hb X fx (wOf H) H) := by
  have e : FailG (Ret := Ret) I hb X fx (wOf H) H ↔ FailOld I hb X fx (wOf H) H :=
    ⟨fun ⟨r, _, o⟩ => ⟨r, o⟩, fun ⟨r, o⟩ => ⟨r, fixedRet H, o⟩⟩
  rw [propext e]

/-- (b) The corrected averaged theorem implies the old-placement reading:
`TASB.deployed_charge` with an extra cross-world premise `∀ H, Ret`.  The
corrected statement therefore covers every adversary the old reading covered
and drops that cross-world premise. -/
theorem grouped_implies_fixed {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib}
    (I : Impl L V0 VL) (hb : HeadlineB S R) (X : ExecB S R) (Ex : Expect X.Oracle)
    (fx : X.Fixed) (wOf : X.Oracle → X.World) (r : X.Oracle → Rat) (T : Rat)
    (grouped : Ex.E (fun H => max (r H) (ind (FailG (Ret := Ret) I hb X fx (wOf H) H))) ≤ T)
    (fixedRet : ∀ H, Ret (ctxB X fx (wOf H) H)) :
    Ex.E (fun H => max (r H) (ind (FailOld I hb X fx (wOf H) H))) ≤ T := by
  have same : (fun H => max (r H) (ind (FailG (Ret := Ret) I hb X fx (wOf H) H))) =
      (fun H => max (r H) (ind (FailOld I hb X fx (wOf H) H))) := by
    funext H
    rw [indicator_eq_of_fixed I hb X fx wOf fixedRet H]
  rw [← same]
  exact grouped

/-- (c) Trust reading of the retained rows: at every world where the actual
entries ran, the runtime supplied admission and persistence at those entries.
Then the corrected failure event drops no world of the old one. -/
theorem indicator_eq_of_trust {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib}
    (I : Impl L V0 VL) (hb : HeadlineB S R) (X : ExecB S R) (fx : X.Fixed)
    (w : X.World) (H : X.Oracle)
    (trust : Runs S I (ctxB X fx w H) → Ret (ctxB X fx w H)) :
    ind (FailG (Ret := Ret) I hb X fx w H) = ind (FailOld I hb X fx w H) := by
  have e : FailG (Ret := Ret) I hb X fx w H ↔ FailOld I hb X fx w H :=
    ⟨fun ⟨r, _, o⟩ => ⟨r, o⟩, fun ⟨r, o⟩ => ⟨r, trust r, o⟩⟩
  rw [propext e]

/-- (a) The only per-world difference: the corrected failure event is the old
one intersected with `Ret` at the same world. -/
theorem failG_eq {R : RecSig S} {L : PoolLib} {V0 : V2Lib} {VL : VLib}
    (I : Impl L V0 VL) (hb : HeadlineB S R) (X : ExecB S R) (fx : X.Fixed)
    (w : X.World) (H : X.Oracle) :
    FailG (Ret := Ret) I hb X fx w H ↔ FailOld I hb X fx w H ∧ Ret (ctxB X fx w H) :=
  ⟨fun ⟨r, t, o⟩ => ⟨⟨r, o⟩, t⟩, fun ⟨⟨r, o⟩, t⟩ => ⟨r, t, o⟩⟩

#print axioms runs_iff
#print axioms exec_same
#print axioms top_splitB_grouped
#print axioms deployed_charge_grouped
#print axioms indicator_eq_of_fixed
#print axioms grouped_implies_fixed
#print axioms indicator_eq_of_trust
#print axioms failG_eq

end RSL.NFB
