import AspisR1ProducerRelease47.Interpolate48
import R1Z.ProverCommitInverse48
import R1Z.ProverCommitBasisCounter47
/-! The independently extracted interpolation inverse owner has the retained
fixed-chain Result, including its raw-zero assertion. -/
set_option autoImplicit false
namespace R1Z.ProverCommitInterpolationInverse48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47

theorem square_counter (x : U32) (n : Nat) (left : U8) (hleft : left.val=n) :
    square_ref x left=ProverCommitInverse48.square_owned x n := by
  induction n generalizing x left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    rw [square_ref,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have ht : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    rw [square_ref,ProverCommitInverse48.square_owned]
    simp only [hn,if_false,lift,bind_tc_ok]
    have tail : ∀ y, square_ref y (U8.wrapping_sub left 1#u8)=ProverCommitInverse48.square_owned y n :=
      fun y => ih y _ ht
    simp only [tail]

theorem source_square (x : U32) (left : U8) :
    square_ref x left=ProverCommitInverse48.square_owned x left.val := square_counter x left.val left rfl

theorem source_inverse (x : U32) : inverse_ref x=ProverCommitInverse48.inverse_owned x := by
  unfold inverse_ref ProverCommitInverse48.inverse_owned
  have guard : ((x != 0#u32)=true) ↔ x≠0#u32 := by simp
  simp only [massert,guard,source_square,show (2#u8).val=2 from rfl,show (4#u8).val=4 from rfl,
    show (8#u8).val=8 from rfl]

theorem inverse_exact (x : U32) (hx : x≠0#u32) :
    ∃ y : U32, inverse_ref x=ok y ∧ y.val < AspisCircleGroupOrder.P ∧
      ProverCommitInverse48.decode y=(ProverCommitInverse48.decode x)⁻¹ := by
  refine ⟨ProverCommitInverse48.inverseWord x,?_,ProverCommitInverse48.inverse_canonical x,
    ProverCommitInverse48.inverse_decode x⟩
  rw [source_inverse,ProverCommitInverse48.inverse_result]
  simp [hx]

#print axioms square_counter
#print axioms source_square
#print axioms source_inverse
#print axioms inverse_exact
end R1Z.ProverCommitInterpolationInverse48
