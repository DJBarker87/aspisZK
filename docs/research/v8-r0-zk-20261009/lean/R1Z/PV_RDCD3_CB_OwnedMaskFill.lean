import R1Z.PV_RDCD3_CB_OwnedMaskLeaves
import R1Z.PV_RDCD3_CB_ForwardLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_OwnedMaskFill
open Aeneas Aeneas.Std Result PV_RDCD3_CB_ForwardRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
def c1Exponents : Array Usize 16#usize := Array.make 16#usize
  [0#usize,2#usize,4#usize,6#usize,8#usize,10#usize,12#usize,14#usize,
   16#usize,18#usize,20#usize,22#usize,24#usize,26#usize,13#usize,25#usize]
def maskExponents : Array Usize 10#usize := Array.make 10#usize
  [1#usize,3#usize,5#usize,7#usize,9#usize,11#usize,15#usize,17#usize,19#usize,21#usize]
def step {N : Usize} (data : Array Q N) (exponents : Array Usize N)
    (i : Usize) (coeff : Coeff) : Result Coeff := do
  let e ← Array.index_usize exponents i
  let q ← Array.index_usize data i
  let coord ← lift (i &&& 3#usize)
  let q ← PV_RDCD3_CB_OwnedMask.owned.tower q coord
  PV_RDCD3_CB_OwnedMask.owned.cell coeff e q

theorem c1 (data : Array Q 16#usize) (fuel : Nat) (i : Usize) (coeff : Coeff)
    (rank : i.val+fuel=16) : PV_RDCD3_CB_OwnedMask.owned.fill_c1 data coeff i =
    PV_RDCD3_CB_ForwardLoop.finite (step data c1Exponents) fuel i coeff := by
  induction fuel generalizing i coeff with
  | zero =>
    have done : ¬i<16#usize := by change ¬i.val<16;omega
    rw [PV_RDCD3_CB_OwnedMask.owned.fill_c1]
    simp only [done,if_false,PV_RDCD3_CB_ForwardLoop.finite]
  | succ fuel ih =>
    have more : i<16#usize := by change i.val<16;omega
    have adv := advance_val i 16#usize more
    rw [PV_RDCD3_CB_OwnedMask.owned.fill_c1]
    simp only [more,if_true,PV_RDCD3_CB_ForwardLoop.finite,step,c1Exponents,lift,bind_tc_ok,bind_assoc_eq]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih (advance i) _ (by omega)
theorem mask (data : Array Q 10#usize) (fuel : Nat) (i : Usize) (coeff : Coeff)
    (rank : i.val+fuel=10) : PV_RDCD3_CB_OwnedMask.owned.fill_mask data coeff i =
    PV_RDCD3_CB_ForwardLoop.finite (step data maskExponents) fuel i coeff := by
  induction fuel generalizing i coeff with
  | zero =>
    have done : ¬i<10#usize := by change ¬i.val<10;omega
    rw [PV_RDCD3_CB_OwnedMask.owned.fill_mask]
    simp only [done,if_false,PV_RDCD3_CB_ForwardLoop.finite]
  | succ fuel ih =>
    have more : i<10#usize := by change i.val<10;omega
    have adv := advance_val i 10#usize more
    rw [PV_RDCD3_CB_OwnedMask.owned.fill_mask]
    simp only [more,if_true,PV_RDCD3_CB_ForwardLoop.finite,step,maskExponents,lift,bind_tc_ok,bind_assoc_eq]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih (advance i) _ (by omega)
#print axioms c1
#print axioms mask
end R1Z.PV_RDCD3_CB_OwnedMaskFill
