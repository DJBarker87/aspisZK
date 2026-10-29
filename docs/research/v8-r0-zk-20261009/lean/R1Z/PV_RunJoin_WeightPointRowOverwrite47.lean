import R1Z.PV_RunJoin_WeightMatrixFrame47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRowOverwrite47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightMatrixFrame47 (Frame)

theorem remaining (p : Array K 10#usize) (n : Nat) (m m1 : Matrix) (d : Usize)
    (hb : d.val+n≤5) (hf : Frame m m1 d.val n) :
    PV_RunJoin_WeightPointRows46.remaining p n m d=
      PV_RunJoin_WeightPointRows46.remaining p n m1 d := by
  induction n generalizing m m1 d with
  | zero => rw [PV_RunJoin_WeightMatrixFrame47.done m m1 d.val hf]
  | succ n ih =>
    have hd : d.val<5 := by omega
    have hv : (Usize.wrapping_add d 1#usize).val=d.val+1 :=
      PV_B2_C_MutationTotal.next_val d (by scalar_tac)
    rw [PV_RunJoin_WeightPointRows46.remaining,PV_RunJoin_WeightPointRows46.remaining]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro t _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro a _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro b _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro row _
    simp only [PV_RunJoin_WeightArrayUpdate47.complete m d hd row,
      PV_RunJoin_WeightArrayUpdate47.complete m1 d hd row,bind_tc_ok]
    exact ih _ _ _ (by rw [hv];omega) (by
      rw [hv]
      exact PV_RunJoin_WeightMatrixFrame47.step m m1 d n row hd hf)
#print axioms remaining

theorem complete (p : Array K 10#usize) (m m1 : Matrix) :
    PV_RunJoin_WeightPointRows46.remaining p 5 m 0#usize=
      PV_RunJoin_WeightPointRows46.remaining p 5 m1 0#usize := by
  apply remaining p 5 m m1 0#usize (by decide)
  intro i hi hf
  have hz : (0#usize).val=0 := by scalar_tac
  rw [hz] at hf
  omega
#print axioms complete
end R1Z.PV_RunJoin_WeightPointRowOverwrite47
