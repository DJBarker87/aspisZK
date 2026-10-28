import R1Z.ProverCommitFieldsSource29
import R1Z.ProverCommitFields20
/-! Source-certified finite field-cell fuel. This is a replacement for blind
symbolic recursion in caller gates, with a checked length precondition. -/
set_option autoImplicit false
namespace R1Z.ProverCommitFields29
open Aeneas Aeneas.Std Result AspisR1SimSemantic20
abbrev Bytes := alloc.vec.Vec U8

theorem sub_one (remaining : Usize) (positive : 0<remaining.val) :
    (Usize.wrapping_sub remaining 1#usize).val = remaining.val-1 := by
  rw [Usize.wrapping_sub_val_eq]
  have one : (1#usize).val=1 := by scalar_tac
  rw [one]
  have hb := remaining.hSize
  have hp : 0<UScalar.size .Usize := by rw [UScalar.size_def];positivity
  have he : remaining.val+(UScalar.size .Usize-1) =
      (remaining.val-1)+UScalar.size .Usize := by omega
  rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

/-- Exact extracted source identity for every fuel, including errors,
short suffixes, cloned bytes, wrapping field indices, failure and divergence. -/
theorem finite_source (n : Nat) (remaining : Usize) (row : U8)
    (payload : Bytes) (value : Usize) (count : remaining.val=n) :
    r1_wire.fields29.finite row payload value remaining =
    ProverCommitFields20.finite row payload value n := by
  induction n generalizing remaining payload value with
  | zero =>
    have zero : remaining=0#usize := by scalar_tac
    rw [r1_wire.fields29.finite]
    simp only [zero,if_true,ProverCommitFields20.finite]
  | succ n ih =>
    have nonzero : remaining≠0#usize := by scalar_tac
    have dec : (Usize.wrapping_sub remaining 1#usize).val=n := by
      rw [sub_one remaining (by omega)];omega
    have tailRun : ∀ p v, r1_wire.fields29.finite row p v
        (Usize.wrapping_sub remaining 1#usize) = ProverCommitFields20.finite row p v n :=
      fun p v => ih _ p v dec
    have plus : core.num.Usize.wrapping_add value 1#usize = Usize.wrapping_add value 1#usize := by rfl
    have minus : core.num.Usize.wrapping_sub remaining 1#usize = Usize.wrapping_sub remaining 1#usize := by rfl
    rw [r1_wire.fields29.finite]
    simp only [nonzero,if_false,ProverCommitFields20.finite,lift,bind_tc_ok,plus,minus,tailRun]
    rfl

/-- A meaningful input-size bound, checked by the Kani caller adapter, permits
the fueled source helper to replace the retained unbounded owned validator. -/
theorem bounded_owned (n : Nat) (remaining : Usize) (row : U8)
    (payload : Bytes) (value : Usize) (count : remaining.val=n)
    (bound : payload.val.length<32*(n+1)) :
    r1_wire.fields29.finite row payload value remaining =
    r1_wire.fields20.validate row payload value := by
  rw [finite_source n remaining row payload value count]
  exact (ProverCommitFields20.extracted_finite n row payload value bound).symm

#print axioms sub_one
#print axioms finite_source
#print axioms bounded_owned
#print axioms AspisR1SimSemantic20.r1_wire.fields29.finite
end R1Z.ProverCommitFields29
