import R1Z.PV_RunJoin_WeightCircleSource47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCircleLoop47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K)
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightFactorWrite47 (Matrix)

theorem complete (n : Nat) (fs : Factors) (slot d : Usize) (x : K) (m : Matrix)
    (hr : Array.index_usize fs slot=ok m) (hs : slot.val<5) :
    PV_RunJoin_WeightCircleSource47.lines n fs slot d x=(do
      let m1 ← PV_RunJoin_WeightCircleRows46.remaining n m d x
      ok (Aeneas.Std.Array.set fs slot m1)) := by
  induction n generalizing fs d x m with
  | zero =>
    simp only [PV_RunJoin_WeightCircleSource47.lines,PV_RunJoin_WeightCircleRows46.remaining,bind_tc_ok,
      PV_RunJoin_WeightFactorRestore47.complete fs slot m hr]
  | succ n ih =>
    rw [PV_RunJoin_WeightCircleSource47.lines,PV_RunJoin_WeightCircleRows46.remaining]
    simp only [PV_RunJoin_WeightFactorWrite47.equation,hr,bind_tc_ok,bind_assoc]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro y _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro row _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro m1 _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    rw [ih _ _ next m1 (PV_RunJoin_WeightFactorWrite47.read_set fs slot m1 hs)]
    simp only [PV_RunJoin_WeightFactorWrite47.overwrite]
#print axioms complete
end R1Z.PV_RunJoin_WeightCircleLoop47
