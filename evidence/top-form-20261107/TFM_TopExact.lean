/-
TFM_TopExact: how close the top can come to the EXACT headline shape.

Target not yet established.  Core Lean plus RSL_/TCK_/TAS_ only.  No sorry, no
axiom, no Root0 hypothesis, no hash-injectivity premise.

Finding (TFM_REPORT.md section 1).  The exact shape `Bound ∧ Concl` is NOT
reachable by putting the charged event "inside Outcome", because the event is
not the whole of `FJv_DResult.Outcome`.  Outcome is
  `∃ f s outer pre middle fs ss run tx2,
     P2P_Origin.Fact … (e2.second secondSizes) data2 slot s ∧
     Cons_Native.Calls … s.pub s.proof s.checkpoint tx2 ∧ … ∧
     (bad ∨ P2P_Acceptance.Facts … ∧ …)`
with `bad :=` the charged event.  Only the LAST conjunct carries the event.  The
TX2 second cut `s`, its origin fact and the cohort reader success
`Cons_Native.Calls` are model-TX2 facts; the headline proof obtains them from
`accepted2` (FJv_DNativeAccepted.accepted / FJp_Ret_Rc7Native.accepted), which at
the actual code needs Root0.  So `Event → Outcome` is not available.

What IS reachable (this file, `top_split`): all ten conjuncts other than
Outcome unconditionally, and only Outcome disjoined with the event:
    Bound ∧ Rest ∧ (Outcome ∨ Event).
This is strictly stronger than TAS `top` (`top_split_to_top`), and equals the
exact headline shape off the event (`top_split_exact_off_event`).

Host obligation introduced: `Split.rest`, a Root0-free re-assembly of the
headline's non-Outcome conjuncts from extraction, accepted1, game, queries
(and the retained binders).  Its host proof is the existing FJp_ARCore branch
terms (P6C_Extension.boundary, DrvC_SourceEntry.same_program,
DrvC_Installation.aus1_dictionary, F3X_ModelClaims.claims, FJp_Cost.source_cost,
F3Y_AccountMass.claims, PoolT_Write.accepted_verifier_writes_copy,
Rc2_Events.derive, CPH_Protection.derive, CPH_Trace.derive,
CPH_Recorder.physical, S6N_Installation.facts) plus FJp_Residual.numeric with
F3U_Range.per_attempt / F3U_Numeric.runtime_margin; none of those terms takes
`accepted2`.  It adds no trust and no premise to the headline.
-/
import TAS_Top
set_option autoImplicit false

namespace RSL.TFM
open RSL.TAS
open TX2_241 (V2Lib Dom064)
open TX1_345 (S1Lib)

/-- The headline conclusion split into its Outcome conjunct and the other ten. -/
structure Split (S : Sig) where
  /-- Conjuncts 1–3 and 5–11 of `AspisR1.RPx_Deployed.deployed` (P6 boundary,
  driver/SDK equalities, claims and the three numeric clauses, copy facts,
  Rc2_Events, CPH Protection/Trace/Recorder, S6N_Installation). -/
  Rest : S.Ctx → S.First → S.Second → Prop
  /-- Conjunct 4, `FJv_DResult.Outcome … (BinRawByteCollisionTargets.event …)`. -/
  Outcome : S.Ctx → S.First → S.Second → Prop
  /-- Host: reassociation of the eleven-fold conjunction (propositional). -/
  concl_iff : ∀ c n1 n2, S.Concl c n1 n2 ↔ Rest c n1 n2 ∧ Outcome c n1 n2
  /-- Host: the Root0-free sub-lemma (no `accepted2`, no Root0). -/
  rest : ∀ c n1 n2, S.Extraction c n1 n2 → S.Accepted1 c n1 → S.Game c n1 n2 →
    S.Queries c n1 → Rest c n1 n2

/-- The split top: every non-Outcome conjunct unconditionally; Outcome or the
headline's charged event. -/
theorem top_split (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c)) := by
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ (er.route1 c frame trace)) ok1 out1
  -- the ten non-Outcome conjuncts: Root0-free
  have rest := sp.rest c _ _ ext acc1 game queries
  refine ⟨bound, rest, ?_⟩
  rcases nmf.root0_or_event c hx weak ok2 acc1 game ext queries with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo nmn
      (S.args2 c) (S.state2 c) (S.env2 c) (er.route2 c frame trace) (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl ((sp.concl_iff c _ _).mp (hl.deployed c _ _ ext acc1 acc2 game queries)).2
  · exact Or.inr (cs.event_eq c ev)

/-- The split form implies the TAS form. -/
theorem top_split_to_top (S : Sig) (sp : Split S) (c : S.Ctx) (n1 : S.First) (n2 : S.Second)
    (h : S.Bound c n1 n2 ∧ sp.Rest c n1 n2 ∧ (sp.Outcome c n1 n2 ∨ S.Event c n1)) :
    S.Bound c n1 n2 ∧ (S.Concl c n1 n2 ∨ S.Event c n1) := by
  rcases h with ⟨b, r, o | e⟩
  · exact ⟨b, Or.inl ((sp.concl_iff c n1 n2).mpr ⟨r, o⟩)⟩
  · exact ⟨b, Or.inr e⟩

/-- Off the event, the split form is the exact headline shape. -/
theorem top_split_exact_off_event (S : Sig) (sp : Split S) (c : S.Ctx) (n1 : S.First)
    (n2 : S.Second)
    (h : S.Bound c n1 n2 ∧ sp.Rest c n1 n2 ∧ (sp.Outcome c n1 n2 ∨ S.Event c n1))
    (clean : ¬ S.Event c n1) :
    S.Bound c n1 n2 ∧ S.Concl c n1 n2 := by
  rcases h with ⟨b, r, o | e⟩
  · exact ⟨b, (sp.concl_iff c n1 n2).mpr ⟨r, o⟩⟩
  · exact absurd e clean

/-- What the exact shape would need: the event must imply all of Outcome.  The
headline's Outcome supplies only its last conjunct from the event (see header),
so this hypothesis is NOT available; the theorem records the gap precisely. -/
theorem exact_iff_event_gives_outcome (S : Sig) (sp : Split S) (c : S.Ctx) (n1 : S.First)
    (n2 : S.Second)
    (h : S.Bound c n1 n2 ∧ sp.Rest c n1 n2 ∧ (sp.Outcome c n1 n2 ∨ S.Event c n1))
    (eventOutcome : S.Event c n1 → sp.Outcome c n1 n2) :
    S.Bound c n1 n2 ∧ S.Concl c n1 n2 := by
  rcases h with ⟨b, r, o | e⟩
  · exact ⟨b, (sp.concl_iff c n1 n2).mpr ⟨r, o⟩⟩
  · exact ⟨b, (sp.concl_iff c n1 n2).mpr ⟨r, eventOutcome e⟩⟩

/-! ## ALLOC: the abort-indicator allocator instance

Transcription (not an import) of `Aeneas.Std.Result`'s three constructors,
`S2W_Trace.thenResult`, `S2W_D189Wrappers.Allocator` and
`S2W_D189Wrappers.reserve`, verbatim up to the error payload.  The host proof
is the same induction.  With `A := Bool` and the allocator below, the
allocator part of `accepted1/2` holds at `state = final = true`, and an
invocation whose allocations aborted is modelled by `state = false`, whose
wrapper fails before the native call (an aborted, rolled-back step). -/
namespace Alloc

inductive Res (α : Type) where
  | ok : α → Res α
  | fail : Res α
  | div : Res α

def thenResult {α β : Type} (r : Res α) (k : α → Res β) : Res β :=
  match r with
  | .ok a => k a
  | .fail => .fail
  | .div => .div

structure Allocator (A : Type) where
  allocate : A → Nat → Res A
  cleanup : A → Res A

def reserve {A : Type} (allocator : Allocator A) : List Nat → A → Res A
  | [], state => .ok state
  | size :: sizes, state => thenResult (allocator.allocate state size)
      (fun next => reserve allocator sizes next)

/-- `true`: every allocation of this invocation succeeds; `false`: one aborts. -/
def abortIndicator : Allocator Bool where
  allocate b _ := if b then .ok b else .fail
  cleanup b := if b then .ok b else .fail

theorem reserve_true (sizes : List Nat) : reserve abortIndicator sizes true = .ok true := by
  induction sizes with
  | nil => rfl
  | cons n ns ih =>
    show thenResult (abortIndicator.allocate true n) (fun next => reserve abortIndicator ns next) = _
    exact ih

theorem cleanup_true : abortIndicator.cleanup true = .ok true := rfl

theorem reserve_false (n : Nat) (ns : List Nat) :
    reserve abortIndicator (n :: ns) false = .fail := by
  simp [reserve, abortIndicator, thenResult]

/-- The allocator part of `accepted1`/`accepted2` at the instance. -/
theorem allocator_part (sizes : List Nat) :
    ∃ m, reserve abortIndicator sizes true = .ok m ∧ abortIndicator.cleanup m = .ok true :=
  ⟨true, reserve_true sizes, cleanup_true⟩

end Alloc

#print axioms top_split
#print axioms top_split_to_top
#print axioms top_split_exact_off_event
#print axioms exact_iff_event_gives_outcome
#print axioms Alloc.reserve_true
#print axioms Alloc.reserve_false
#print axioms Alloc.allocator_part

end RSL.TFM
