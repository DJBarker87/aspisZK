import LPm_SixPoints
set_option autoImplicit false
namespace AspisR1.LPm_PointLength
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort AspisR1CurrentPreparedClaim

theorem length {H : Type} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array Concrete.E 29#usize} {point : Usize} {iter : LPm_PointLoop.Range}
    {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : LPm_PointLoop.Trace sem y1 g point iter s xs out)
    (last : iter.end.val=29) (bound : iter.start.val≤29) :
    xs.length=29-iter.start.val := by
  induction tr with
  | done iter iter' s out next finish =>
    have h := ClaimTrace.next_none_bound iter iter' next
    simp only [List.length_nil]
    omega
  | @step iter iter' s s' out xs l v q next read weight cv cq count push tail ih =>
    obtain ⟨hl,active,start,finish⟩ := ClaimTrace.next_some_step iter iter' l next
    have e : iter'.end.val=29 := finish.trans last
    have b : iter'.start.val≤29 := by omega
    have n := ih e b
    simp only [List.length_cons]
    omega

/-- The actual iterator observations determine every one of the six fold
lengths. No supplied length, public sum, or whole-loop equality is required. -/
theorem all_six {H : Type} (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array Concrete.E 29#usize)
    (point : Fin 6 → Usize) (number : ∀ i, (point i).val=i.val)
    (xs : Fin 6 → List (NE×NQ)) (out : Fin 6 → NE)
    (tr : ∀ i, LPm_PointLoop.Trace sem y1 g (point i)
      {start:=0#usize, «end»:=29#usize} LPm_PublicTwentyNine.zero (xs i) (out i)) :
    ∀ i, (xs i).length=29 ∧ (point i).val<6 ∧
      verifier.prepared_claim_dot_loop LPm_PointLoop.ops inst
        {start:=0#usize, «end»:=29#usize} sem y1 g (point i)
        (statePort LPm_PublicTwentyNine.zero)=ok (.Ok (ePort (out i))) ∧
      ∃ last, LPm_PublicFold.Bounded last 29 ∧
        LPm_PublicFold.meaning last=LPm_PublicFold.fold
          (LPm_PublicFold.meaning LPm_PublicTwentyNine.zero) (xs i) ∧
        FIo_Native.fast_pairing.EbyKDot.finish last=ok (out i) := by
  have sizes : ∀ i, (xs i).length=29 := by
    intro i
    simpa only [Nat.sub_zero] using length (tr i) rfl (by decide)
  intro i
  exact ⟨sizes i,LPm_SixPoints.all_six inst sem y1 g point number xs out sizes tr i⟩

#print axioms length
#print axioms all_six
end AspisR1.LPm_PointLength
