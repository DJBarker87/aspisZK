import NKO_C09Core
set_option autoImplicit false
noncomputable section
namespace NKO_C09
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Actual source branch supplies the native domains; no successful child or
caller length is added to the positive-root inventory. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (Holds proof)
  (run wr rr merkle finish d pub proof ck hash none) := by
 unfold run
 apply NKE_Entered.bind_all
 · apply NKE_EventAll.record_all
   exact True.intro
 · intro reply entered
   cases reply with
   | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,NKE_Entered.lift_ok]
    exact NKE_EventAll.lift_all _ _
   | Ok pair =>
    rcases pair with ⟨p,a⟩
    have fields := NKE_ResumeWidth.returned wr d ck proof pub hash p a entered
    have width : a.weights.val.length=64 := fields.width
    simp only [core.result.Result.Insts.CoreOpsTry.branch,NKE_Entered.lift_ok]
    by_cases wrong : (a.next != NHT_Constants.compact.SPLIT)=true
    · rw [if_pos wrong]
      exact NKE_EventAll.lift_all _ _
    · rw [if_neg wrong]
      have same : a.next=NHT_Constants.compact.SPLIT := by
       apply UScalar.eq_of_val_eq
       simpa using wrong
      have start : a.next=10#usize := by
       rw [same]
       unfold NHT_Constants.compact.SPLIT
       rfl
      simp only [alloc.vec.Vec.deref_mut,lift,NKE_Entered.lift_ok,
       NKO_Offsets.inactive,NKO_Offsets.round0,NKO_Offsets.folded,NKO_Offsets.round1,
       NKO_Offsets.final_message,NKO_Offsets.openings]
      apply NKE_Entered.bind_all
      repeat' first
      | nke_zeta
      | nko_c03_bind
      | nke_intro
      | nke_lift
      | nke_pure
      | nko_c09_record
      | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
      | split
#print axioms source
end NKO_C09
