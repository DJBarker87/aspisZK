import LPm_PointLoop
set_option autoImplicit false
namespace AspisR1.LPm_SixPoints
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort AspisR1CurrentPreparedClaim

theorem erase {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array Concrete.E 29#usize} {point : Usize} {iter : LPm_PointLoop.Range}
    {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : LPm_PointLoop.Trace sem y1 g point iter s xs out) :
    ∃ last, LPm_PublicFold.Trace xs s last ∧
      FIo_Native.fast_pairing.EbyKDot.finish last=ok out := by
  induction tr with
  | done iter iter' s out next finish => exact ⟨s,.done s,finish⟩
  | @step iter iter' s s' out xs l v q next read weight cv cq count push tail ih =>
    obtain ⟨last,steps,finish⟩ := ih
    exact ⟨last,.step cv cq push steps,finish⟩

/-- All six point folds share the SAME caller sem/y1/g. The full cohort loop
Result and its 29-step field sum follow from linked local native transitions.
This theorem does not supply the missing native whole prepared_claim join. -/
theorem all_six {H : Type} (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
    (point : Fin 6 → Usize) (number : ∀ i, (point i).val=i.val)
    (xs : Fin 6 → List (NE×NQ)) (out : Fin 6 → NE)
    (size : ∀ i, (xs i).length=29)
    (tr : ∀ i, LPm_PointLoop.Trace sem y1 g (point i)
      {start:=0#usize, «end»:=29#usize} LPm_PublicTwentyNine.zero (xs i) (out i)) :
    ∀ i, (point i).val<6 ∧
      verifier.prepared_claim_dot_loop LPm_PointLoop.ops inst
        {start:=0#usize, «end»:=29#usize} sem y1 g (point i)
        (statePort LPm_PublicTwentyNine.zero)=ok (.Ok (ePort (out i))) ∧
      ∃ last, LPm_PublicFold.Bounded last 29 ∧
        LPm_PublicFold.meaning last=LPm_PublicFold.fold
          (LPm_PublicFold.meaning LPm_PublicTwentyNine.zero) (xs i) ∧
        FIo_Native.fast_pairing.EbyKDot.finish last=ok (out i) := by
  intro i
  obtain ⟨last,steps,finish⟩ := erase (tr i)
  obtain ⟨bound,value⟩ := LPm_PublicTwentyNine.source (xs i) last (size i) steps
  exact ⟨by rw [number]; exact i.isLt,
    LPm_PointLoop.source inst (tr i),last,bound,value,finish⟩

#print axioms erase
#print axioms all_six
end AspisR1.LPm_SixPoints
