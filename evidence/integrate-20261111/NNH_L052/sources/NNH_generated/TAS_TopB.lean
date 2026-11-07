/-
TAS_TopB: the split-B top with the Realizes construction, and the averaging
step at that instantiation (stand-in level).

Target not yet established.  Core Lean plus RSL_/TCK_/TAS_/TFM_/EVB_ only.  No
sorry, no axiom declaration, no Root0 hypothesis, no hash-injectivity premise.

Owner decision 2026-11-07 (C3-BIN, newest entries): split top form, option B
with Realizes.  Binding conditions, and where each is met in this file:
  (1) the adversary stays universally quantified: `fx : X.Fixed` carries `a`
      and is a universally quantified argument of every theorem below; no
      theorem fixes `a` (in particular no constant adversary);
  (2) the inclusion "actual TX2 accepted, Root0 failing ⇒ E_rec" is proved,
      not assumed: it is `EVB.NNC_NMFPrimeB.root0_or_rec`, a deliverable whose
      host proof is the NNC_ fold with the selector generalised; no theorem
      here takes it as a bare hypothesis about the conclusion;
  (3) BOTH events are re-targeted: the outer alternative is `R.EventRec`
      (E_rec) and the Root0 arm returns `hb.OutcomeRec` (Outcome with
      `bad := E_rec`); this file instantiates `EVB.top_splitB_full`, never
      `EVB.top_splitB` (which keeps the adopted inner `bad := E_head`);
  (4) the pair is INSTANTIATED from the adversary's execution at H:
      `ctxB X fx w H` puts `i := first fx H` (= (eval H a.first).2) and
      `j := second fx w H i` (= (eval H (a.second i saved post1 final1)).2)
      into the binder block, so `realizes` holds by `⟨rfl, rfl⟩`
      (`realizes_by_construction`).  Realizes never occurs as a hypothesis of
      `top_splitB` or of `deployed_charge`, and `realizes_everywhere` shows
      it holds at every world of the instantiation, so it excludes no H;
  (5) the averaged statement `deployed_charge` is over all H (an abstract
      expectation `Ex.E` over every oracle), with no conditioning.

Open host check RZ-STATE (TAS_G0_BRIEF.md section 6).  `In1`/`In2` carry the
allocator state, and `ART_PartialAccount.firstSyntax`/`secondSyntax` pass
`i.state`/`j.state` to the model wrapper.  Ruling (bo) fixes state1 = state2 :=
true, while condition (4) defines them as the adversary's outputs.  The two
agree only at worlds where the adversary outputs `true`.  At any other world
the host cannot satisfy both: if the context stores the adversary's state,
`realizes_mk` holds but the physical acceptance (state `true`) and
`RecSelect.selects` (whose account run then has a rejecting TX1 model reply)
no longer match; if it stores `true`, `realizes_mk` fails there, and Realizes
would act as a filter.  This file is correct at stand-in level because
`ExecB.realizes_mk` and `RecSelect` are fields; it does not resolve RZ-STATE,
which is escalated to the owner through the lead.

Stand-ins: `ExecB` (how the headline binder block is built from the
adversary's run) and `Expect` (the expectation over H) are FIELDS of
structures, never `opaque`/`axiom`; each field names its host term.
-/
import EVB_EventB
set_option autoImplicit false

namespace RSL.TASB
open RSL.TAS RSL.TFM RSL.EVB
open TX2_241 (V2Lib Dom064)
open TX1_345 (S1Lib)

/-! ## 1. Building the context from the adversary's execution -/

/-- Execution stand-in.  Host: `Fixed` is the binder block of
`AspisR1.RPx_Deployed.deployed` restricted to the binders that do not depend
on the oracle or on the deployed pair (L sdk copy std, allocator :=
abortIndicator (ruling (bo)), missing := NND_Missing.instance (ruling (s)),
indexError reservation hashv admission1/2 sha256 p1 syscall root length prior
words D, the adversary `a`, Q0 Q1).  `World` is the per-world remainder other
than H and the pair (saved post1 final1 post2 final2 p t u actions
RuntimePersistence); a theorem below quantifies over every function
`Oracle → World`, so these binders may depend on H arbitrarily. -/
structure ExecB (S : Sig) (R : RecSig S) where
  Fixed : Type
  World : Type
  /-- `Bytes → State`, the random oracle H. -/
  Oracle : Type
  /-- `GExq_AccountExperiment.FirstInputs A` (`⟨e1, data1, state1⟩`). -/
  In1 : Type
  /-- `GExq_AccountExperiment.SecondInputs A` (`⟨e2, data2, slot, state2⟩`). -/
  In2 : Type
  /-- `(eval H a.first).2`. -/
  first : Fixed → Oracle → In1
  /-- `(eval H (a.second i saved post1 final1)).2` (saved/post1/final1 from `World`). -/
  second : Fixed → World → Oracle → In1 → In2
  /-- The binder block with `H` and `e1 data1 state1 := i`, `e2 data2 slot state2 := j`
  (a structure constructor at the host). -/
  build : Fixed → World → Oracle → In1 → In2 → S.Ctx
  /-- Host: `Iff.rfl` — `Realizes` (the owner's statement) is exactly these two equations
  at the binders `build` installs. -/
  realizes_mk : ∀ fx w H i j, R.Realizes (build fx w H i j) ↔ (first fx H = i ∧ second fx w H i = j)
  /-- Host: `rfl` — `missing` is installed as `NND_Missing.instance` in `Fixed`. -/
  exhibited_mk : ∀ fx w H i j, S.Exhibited (build fx w H i j)
  /-- L154 statement parameter on the adversary: `∀ H, (ARW_Induced.issued model1 copy
  allocator CPH_Program.verifier a H).length ≤ Q0+Q1`. -/
  QueriesF : Fixed → Prop
  /-- Host: `id` — `queries` mentions only `a`, copy, allocator, Q0, Q1 and native1 := model1. -/
  queries_mk : ∀ fx w H i j, QueriesF fx → S.Queries (build fx w H i j) (S.model1 (build fx w H i j))
  /-- E_rec at H (`FJp_Mass.bounded`'s event): mentions cfg hashv copy allocator a Q0 Q1 H only. -/
  ERec : Fixed → Oracle → Prop
  /-- Host: `Iff.rfl`. -/
  eventRec_mk : ∀ fx w H i j, R.EventRec (build fx w H i j) ↔ ERec fx H

variable {S : Sig} {R : RecSig S}

/-- The context of world H: the pair is the adversary's own output at H. -/
def ctxB (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) : S.Ctx :=
  X.build fx w H (X.first fx H) (X.second fx w H (X.first fx H))

/-- Condition (4): Realizes holds by construction. -/
theorem realizes_by_construction (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) :
    R.Realizes (ctxB X fx w H) :=
  (X.realizes_mk _ _ _ _ _).mpr ⟨rfl, rfl⟩

/-- Realizes is not a filter: at the instantiation it holds at EVERY world,
for every choice of the per-world binders. -/
theorem realizes_everywhere (X : ExecB S R) (fx : X.Fixed) (wOf : X.Oracle → X.World) :
    ∀ H, R.Realizes (ctxB X fx (wOf H) H) :=
  fun H => realizes_by_construction X fx (wOf H) H

/-- Realizes carries no content beyond the defining equations: a context
built by `build` satisfies it only at the adversary's outputs. -/
theorem realizes_only_run (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (i : X.In1) (j : X.In2) (h : R.Realizes (X.build fx w H i j)) :
    X.build fx w H i j = ctxB X fx w H := by
  obtain ⟨h1, h2⟩ := (X.realizes_mk _ _ _ _ _).mp h
  subst h1; subst h2
  rfl

/-- The actual-run facts of the deployed pair at a context: the attack's
success antecedent.  `Realizes` is NOT one of them. -/
structure Runs (S : Sig) {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : Impl L V0 VL)
    (c : S.Ctx) : Prop where
  frame : S.GameFrame c
  trace : S.TraceRep c I.entry
  ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s')
  out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c))
  ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')
  out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))

/-! ## 2. The split-B top at the instantiation -/

/-- `top_splitB`: the top in split-B form, with the deployed pair instantiated
from the adversary's execution at H, so the owner's `realizes` premise is
discharged by `rfl`.  Both events are E_rec (`EVB.top_splitB_full`). -/
theorem top_splitB (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
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
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H) := by
  have h := top_splitB_full S L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo nmn
    g1a R rs hb nmfB r0 a1 a2 a3 a4 a5 er (ctxB X fx w H)
    (X.exhibited_mk _ _ _ _ _) (X.queries_mk _ _ _ _ _ queries) run.frame run.trace
    (realizes_by_construction X fx w H) run.ok1 run.out1 run.ok2 run.out2
  rcases h with ⟨b, r, o | e⟩
  · exact ⟨b, r, Or.inl o⟩
  · exact ⟨b, r, Or.inr ((X.eventRec_mk _ _ _ _ _).mp e)⟩

/-- The per-world inclusion the averaging uses: a successful actual run whose
Outcome (bad := E_rec) fails lies in E_rec at the SAME H. -/
theorem fail_sub_rec (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
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
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) (queries : X.QueriesF fx)
    (fail : Runs S I (ctxB X fx w H) ∧
      ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))) :
    X.ERec fx H := by
  rcases (top_splitB L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo nmn g1a rs hb
    nmfB r0 a1 a2 a3 a4 a5 er X fx w H queries fail.1).2.2 with o | e
  · exact absurd o fail.2
  · exact e

/-! ## 3. Averaging over H at the instantiation -/

/-- Expectation over the oracle.  Host: `lazyMean J emptyTable f` for the
joint program `J := F3U_Joint.program …` whose view determines the per-world
quantities (see TAS_G0_BRIEF.md, AVG); `mono` is
`AllAddressFiatShamir.lazyMean_mono_of_eval`, `add` is `lazyMean_add` (the
two facts `F3U_Averaging.charge` uses). -/
structure Expect (Ω : Type) where
  E : (Ω → Rat) → Rat
  mono : ∀ f g : Ω → Rat, (∀ x, f x ≤ g x) → E f ≤ E g
  add : ∀ f g : Ω → Rat, E (fun x => f x + g x) = E f + E g

/-- Indicator (classical decidability, as the host `indicator`). -/
noncomputable def ind (p : Prop) : Rat := by
  classical
  exact if p then 1 else 0

theorem ind_def (p : Prop) [Decidable p] : ind p = if p then 1 else 0 := by
  unfold ind
  congr

/-- Condition (5): the deployed per-attempt failure, averaged over ALL H, is
at most the SAME budget `T` that already bounds `m + 1_{E_rec}` (E_rec is
charged once).  The per-world loss is `max r 1_{fail}` with
`fail H := Runs at ctxB ∧ ¬ OutcomeRec at ctxB` — the attack succeeded at H
and the headline's Outcome failed.  There is no Realizes hypothesis, no
conditioning and no restriction on H; `wOf` lets every non-pair binder depend
on H arbitrarily, and `fx` (which carries the adversary) is arbitrary.
Inputs from the host: `each` (per-world `r ≤ m + 1_{E_rec}`, from
`FJp_Mass.bounded`), `hm` (`0 ≤ m`), and `budget` (`E m + E 1_{E_rec} ≤ T`,
the existing `failureModel ≤ total (Q0+Q1)` chain). -/
theorem deployed_charge (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
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
    (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed) (wOf : X.Oracle → X.World)
    (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H))))) ≤ T := by
  classical
  have pointwise : ∀ H, max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H)))) ≤ m H + ind (X.ERec fx H) := by
    intro H
    rw [ind_def, ind_def]
    have e := each H
    rw [ind_def] at e
    exact no_second_charge (r H) (m H) (X.ERec fx H) _ (hm H) e
      (fun f => fail_sub_rec L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo nmn
        g1a rs hb nmfB r0 a1 a2 a3 a4 a5 er X fx (wOf H) H queries f)
  have h1 := Ex.mono _ _ pointwise
  rw [Ex.add] at h1
  exact Rat.le_trans h1 budget

#print axioms realizes_by_construction
#print axioms realizes_everywhere
#print axioms realizes_only_run
#print axioms top_splitB
#print axioms fail_sub_rec
#print axioms deployed_charge

end RSL.TASB
