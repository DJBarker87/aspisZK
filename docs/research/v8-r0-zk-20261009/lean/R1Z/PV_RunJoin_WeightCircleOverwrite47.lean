import R1Z.PV_RunJoin_WeightMatrixFrame47
import R1Z.PV_RunJoin_WeightCircleRows46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCircleOverwrite47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightMatrixFrame47 (Frame)

theorem remaining (n : Nat) (m m1 : Matrix) (d : Usize) (x : K)
    (hb : d.val+n≤5) (hf : Frame m m1 d.val n) :
    PV_RunJoin_WeightCircleRows46.remaining n m d x=
      PV_RunJoin_WeightCircleRows46.remaining n m1 d x := by
  induction n generalizing m m1 d x with
  | zero => rw [PV_RunJoin_WeightMatrixFrame47.done m m1 d.val hf]
  | succ n ih =>
    have hd : d.val<5 := by omega
    have hv : (Usize.wrapping_add d 1#usize).val=d.val+1 :=
      PV_B2_C_MutationTotal.next_val d (by scalar_tac)
    rw [PV_RunJoin_WeightCircleRows46.remaining,PV_RunJoin_WeightCircleRows46.remaining]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro y _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro row _
    simp only [PV_RunJoin_WeightArrayUpdate47.complete m d hd row,
      PV_RunJoin_WeightArrayUpdate47.complete m1 d hd row,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih _ _ _ next (by rw [hv];omega) (by
      rw [hv]
      exact PV_RunJoin_WeightMatrixFrame47.step m m1 d n row hd hf)
#print axioms remaining
end R1Z.PV_RunJoin_WeightCircleOverwrite47
