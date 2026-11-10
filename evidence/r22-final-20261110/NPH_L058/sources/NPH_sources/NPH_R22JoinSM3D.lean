import NPH_R22JoinSM3
/-! DIAGNOSTIC (never credited): finish_congr statement bisection with stdout flushes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM3D
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1.NPH_R22JoinSM3

#eval show IO Unit from do IO.println "start"; (← IO.getStdout).flush

theorem t0 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges) (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    FinishModel.finish R B D pub pre t ch obs = FinishModel.finish R B D pub pre t ch obs := by
  sorry
#print axioms t0
#eval show IO Unit from do (← IO.getStdout).flush

theorem t1 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  sorry
#print axioms t1
#eval show IO Unit from do (← IO.getStdout).flush

theorem t2 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hmask : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      m' a a1 q alpha = B.mask a a1 q alpha) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  sorry
#print axioms t2
#eval show IO Unit from do (← IO.getStdout).flush

theorem t3 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hmask : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      m' a a1 q alpha = B.mask a a1 q alpha)
    (hmul : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      u' ch.eta val2 = B.mul ch.eta val2) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  sorry
#print axioms t3
#eval show IO Unit from do (← IO.getStdout).flush

theorem t4 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hmask : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      m' a a1 q alpha = B.mask a a1 q alpha)
    (hmul : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      u' ch.eta val2 = B.mul ch.eta val2)
    (hadd1 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 →
      a' mk q1 = B.add mk q1) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  sorry
#print axioms t4
#eval show IO Unit from do (← IO.getStdout).flush

theorem t5 (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (m' : Array Q 16#usize → Array Q 10#usize → Q → Array Q 10#usize → Result Q)
    (a' u' : Q → Q → Result Q)
    {H : Type} (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (hmask : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize) (q : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      m' a a1 q alpha = B.mask a a1 q alpha)
    (hmul : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      u' ch.eta val2 = B.mul ch.eta val2)
    (hadd1 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 →
      a' mk q1 = B.add mk q1)
    (hadd2 : ∀ (running : Q) (alpha : Array Q 10#usize) (t1 : r1_wire.SemanticTranscript H)
      (v1 : Claims) (val2 : Q) (a : Array Q 16#usize) (a1 : Array Q 10#usize) (a2 : Array Q 29#usize)
      (q mk q1 q2 : Q) (vr : r1_wire.ValidatedRecord) (val3 : Array Q 29#usize) (q3 : Q),
      RoundModel.rounds R D pre t = ok (.Ok (running, alpha, t1)) →
      B.claims pre = ok (.Ok v1) →
      B.terminal pub v1 alpha ch = ok (.Ok val2) →
      B.fromFn 16#usize (FinishModel.closureFn9 D) v1 = ok a →
      B.fromFn 10#usize (FinishModel.closureFn5 D) v1 = ok a1 →
      Array.index_usize v1 0#usize = ok a2 → Array.index_usize a2 27#usize = ok q →
      B.mask a a1 q alpha = ok mk → B.mul ch.eta val2 = ok q1 → B.add mk q1 = ok q2 →
      r1_wire.Prefix.validated_record pre 25#u8 = ok (.Ok vr) →
      R.decode 29#usize vr 87#usize = ok (.Ok val3) →
      Array.index_usize val3 28#usize = ok q3 →
      a' q2 q3 = B.add q2 q3) :
    FinishModel.finish R { B with mask := m', add := a', mul := u' } D pub pre t ch obs =
      FinishModel.finish R B D pub pre t ch obs := by
  sorry
#print axioms t5
#eval show IO Unit from do (← IO.getStdout).flush

end AspisR1.NPH_R22JoinSM3D
