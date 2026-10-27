import R1Z.PV_Src_ExternalSumStep

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalSumLoop
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference PV_Src_ExternalSumStep

def steps (n : Nat) (s : State) (sums : Sums) (col : Usize) : Sums :=
  match n with
  | 0 => sums
  | n+1 => steps n s (sums.set col (cell s col)) (Usize.wrapping_add col 1#usize)

theorem source (n : Nat) (s : State) (sums : Sums) (col : Usize)
    (count : col.val+n=4) :
    poseidon2.builder_reference.external_owned_loop1 s sums col = ok (steps n s sums col) := by
  induction n generalizing sums col with
  | zero =>
    rw [poseidon2.builder_reference.external_owned_loop1,
      if_neg (by rw [UScalar.lt_equiv];simp;omega)]
    rfl
  | succ n ih =>
    rw [PV_Src_ExternalSumStep.step s sums col (by omega)]
    exact ih _ _ (by rw [BuilderRecordsArray.next_val col (by omega)];omega)

#print axioms source
end R1Z.PV_Src_ExternalSumLoop
