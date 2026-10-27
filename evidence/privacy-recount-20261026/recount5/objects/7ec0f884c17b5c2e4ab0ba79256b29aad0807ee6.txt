import R1Z.PV_CBL_DigestUpdateTotal
import R1Z.PV_CBL_DigestUpdateModel
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_DigestUpdateSource
set_option autoImplicit false
theorem loop_source (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (data : Slice U8) (i : Usize)
    (hp : pos.val<64) :
    PV_CBL_DigestSoft.sha_update_soft_owned_loop state blocks buffer pos data i =
      ok (PV_CBL_DigestUpdateModel.value (state,blocks,buffer,pos) (data.val.drop i.val)) := by
  generalize he : data.val.length-i.val=fuel
  induction fuel using Nat.strong_induction_on generalizing state blocks buffer pos i with
  | h fuel ih =>
    rw [PV_CBL_DigestUpdateUnfold.unfold_loop]
    by_cases hi : i.val<data.val.length
    · simp only [PV_CBL_DigestUpdateStep.body data state blocks buffer pos i hp hi,bind_tc_ok,PV_CBL_DigestUpdateStep.continuing]
      have inc := PV_CBL_ArrayStep.increment i (Slice.len data) hi
      let q := PV_CBL_DigestUpdateStep.next state blocks buffer pos data.val[i.val]
      rw [ih _ (by omega) q.1 q.2.1 q.2.2.1 q.2.2.2 (Usize.wrapping_add i 1#usize)
        (PV_CBL_DigestUpdateInvariant.eager state blocks buffer pos _ hp) rfl]
      rw [inc,PV_CBL_DigestUpdateModel.drop_step data.val i.val hi]
      rfl
    · have hn : ¬i<Slice.len data := by change ¬i.val<data.val.length; exact hi
      simp only [PV_CBL_DigestSoft.sha_update_soft_owned_loop.body,if_neg hn,bind_tc_ok]
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
theorem source (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (data : Slice U8) (hp : pos.val<64) :
    PV_CBL_DigestSoft.sha_update_soft_owned state blocks buffer pos data =
      ok (PV_CBL_DigestUpdateModel.value (state,blocks,buffer,pos) data.val) := by
  exact loop_source state blocks buffer pos data 0#usize hp
#print axioms loop_source
#print axioms source
end R1Z.PV_CBL_DigestUpdateSource
