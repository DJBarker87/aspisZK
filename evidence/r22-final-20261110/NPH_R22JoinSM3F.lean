import NPH_R22JoinSM3

/-! NPH_ (R22, SM step 2b): `finish_congr` (statement documented in NPH_R22JoinSM3). Split into its own
module. The reached premises are bundled into the predicates Head/Fill/Tail: the unbundled
28-arrow hypothesis did not elaborate within 180 s (L055-L059), the bundled one in 0.38 s (L060). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM3
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

/-- The reached head: the successful rounds and claims calls of the same finish. -/
def Head (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (running : Q) (alpha : Array Q 10#usize)
    (t1 : r1_wire.SemanticTranscript H) (v1 : Claims) : Prop :=
  RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) ∧ B.claims pre = ok (.Ok v1)

/-- The fromFn and index calls that build the mask arguments. -/
def Fill (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H) (v1 : Claims)
    (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q) : Prop :=
  B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a ∧
  B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 ∧
  Array.index_usize v1 0#usize = ok a2 ∧ Array.index_usize a2 27#usize = ok q

/-- The first add, the row-25 record, its decode and the read of entry 28. -/
def Tail (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) (pre : r1_wire.Prefix)
    (mk q1 q2 : Q) (vr : r1_wire.ValidatedRecord) (val3 : Array Q 29#usize) (q3 : Q) : Prop :=
  B.add mk q1 = ok q2 ∧ r1_wire.Prefix.validated_record pre 25#u8 = ok (.Ok vr) ∧
  R.decode 29#usize vr 87#usize = ok (.Ok val3) ∧ Array.index_usize val3 28#usize = ok q3

theorem finish_congr (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hmask : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q),
      Head R B D pre t running alpha t1 v1 → Fill B D v1 a a1 a2 q →
      m' a a1 q alpha = B.mask a a1 q alpha)
    (hmul : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q),
      Head R B D pre t running alpha t1 v1 → B.terminal pub v1 alpha ch = ok (.Ok val2) →
      u' ch.eta val2 = B.mul ch.eta val2)
    (hadd1 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 : Q),
      Head R B D pre t running alpha t1 v1 → B.terminal pub v1 alpha ch = ok (.Ok val2) →
      Fill B D v1 a a1 a2 q → B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 →
      a' mk q1 = B.add mk q1)
    (hadd2 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 q2 : Q) (vr : r1_wire.ValidatedRecord) (val3 : Array Q 29#usize) (q3 : Q),
      Head R B D pre t running alpha t1 v1 → B.terminal pub v1 alpha ch = ok (.Ok val2) →
      Fill B D v1 a a1 a2 q → B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 →
      Tail R B pre mk q1 q2 vr val3 q3 →
      a' q2 q3 = B.add q2 q3) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  unfold FinishModel.finish
  refine bind_congr_ok _ _ _ (fun r hr => ?_)
  refine bind_congr_ok _ _ _ (fun cf hcf => ?_)
  cases cf with
  | Break res => dsimp only
  | Continue val =>
  obtain ⟨running, alpha, t1⟩ := val
  have hR : RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) := by
    rw [hr, (branch_cont r _).1 hcf]
  refine bind_congr_ok _ _ _ (fun u2 _ => ?_)
  refine bind_congr_ok _ _ _ (fun r1 hr1 => ?_)
  refine bind_congr_ok _ _ _ (fun cf1 hcf1 => ?_)
  cases cf1 with
  | Break res => dsimp only
  | Continue v1 =>
  have hC : B.claims pre = ok (.Ok v1) := by
    have e := (branch_cont r1 _).1 hcf1; subst e; exact hr1
  refine bind_congr_ok _ _ _ (fun r2 hr2 => ?_)
  refine bind_congr_ok _ _ _ (fun r3 hr3 => ?_)
  refine bind_congr_ok _ _ _ (fun cf2 hcf2 => ?_)
  cases cf2 with
  | Break res => dsimp only
  | Continue val2 =>
  have hT : B.terminal pub v1 alpha ch = ok (.Ok val2) := by
    have e := map_err11_cont D r2 r3 val2 hr3 hcf2; subst e; exact hr2
  refine bind_congr_ok _ _ _ (fun u3 _ => ?_)
  refine bind_congr_ok _ _ _ (fun a ha => ?_)
  refine bind_congr_ok _ _ _ (fun a1 ha1 => ?_)
  refine bind_congr_ok _ _ _ (fun a2 ha2 => ?_)
  refine bind_congr_ok _ _ _ (fun q hq => ?_)
  have hm := hmask running alpha t1 v1 a a1 a2 q ⟨hR, hC⟩ ⟨ha, ha1, ha2, hq⟩
  show (m' a a1 q alpha >>= _) = _
  rw [hm]
  refine bind_congr_ok _ _ _ (fun mk hmk => ?_)
  refine bind_congr_ok _ _ _ (fun r4 hr4 => ?_)
  refine bind_congr_ok _ _ _ (fun cf3 hcf3 => ?_)
  cases cf3 with
  | Break res => dsimp only
  | Continue vr =>
  have hV : r1_wire.Prefix.validated_record pre 25#u8 = ok (.Ok vr) := by
    have e := (branch_cont r4 _).1 hcf3; subst e; exact hr4
  refine bind_congr_ok _ _ _ (fun r5 hr5 => ?_)
  refine bind_congr_ok _ _ _ (fun cf4 hcf4 => ?_)
  cases cf4 with
  | Break res => dsimp only
  | Continue val3 =>
  have hD : R.decode 29#usize vr 87#usize = ok (.Ok val3) := by
    have e := (branch_cont r5 _).1 hcf4; subst e; exact hr5
  have hu := hmul running alpha t1 v1 val2 ⟨hR, hC⟩ hT
  show (u' ch.eta val2 >>= _) = _
  rw [hu]
  refine bind_congr_ok _ _ _ (fun q1 hq1 => ?_)
  have hx1 := hadd1 running alpha t1 v1 val2 a a1 a2 q mk q1 ⟨hR, hC⟩ hT ⟨ha, ha1, ha2, hq⟩ hmk hq1
  show (a' mk q1 >>= _) = _
  rw [hx1]
  refine bind_congr_ok _ _ _ (fun q2 hq2 => ?_)
  refine bind_congr_ok _ _ _ (fun q3 hq3 => ?_)
  have hx2 := hadd2 running alpha t1 v1 val2 a a1 a2 q mk q1 q2 vr val3 q3 ⟨hR, hC⟩ hT
    ⟨ha, ha1, ha2, hq⟩ hmk hq1 ⟨hq2, hV, hD, hq3⟩
  show (a' q2 q3 >>= _) = _
  rw [hx2]
  refine bind_congr_ok _ _ _ (fun mt _ => ?_)
  refine bind_congr_ok _ _ _ (fun b _ => ?_)
  (try simp only [circle_eq]) <;> (try dsimp only)
#print axioms finish_congr

end AspisR1.NPH_R22JoinSM3
