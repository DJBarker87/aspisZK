import R1Z.PV_Src_ExternalLaneStep

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalLaneLoop
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference PV_Src_ExternalLaneStep

def steps (n : Nat) (s : State) (sums : Sums) (lane : Usize) : State :=
  match n with
  | 0 => s
  | n+1 => steps n (s.set lane (cell s sums lane)) sums (Usize.wrapping_add lane 1#usize)

theorem source (n : Nat) (s : State) (sums : Sums) (lane : Usize)
    (count : lane.val+n=16) :
    poseidon2.builder_reference.external_owned_loop2 s sums lane = ok (steps n s sums lane) := by
  induction n generalizing s lane with
  | zero =>
    rw [poseidon2.builder_reference.external_owned_loop2,
      if_neg (by rw [UScalar.lt_equiv];simp;omega)]
    rfl
  | succ n ih =>
    rw [PV_Src_ExternalLaneStep.step s sums lane (by omega)]
    exact ih _ _ (by rw [BuilderRecordsArray.next_val lane (by omega)];omega)

#print axioms source
end R1Z.PV_Src_ExternalLaneLoop
