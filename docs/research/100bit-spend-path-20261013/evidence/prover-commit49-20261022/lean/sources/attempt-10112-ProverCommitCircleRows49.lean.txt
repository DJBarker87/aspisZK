import AspisR1ProducerRelease47.CircleFactors49
import R1Z.ProverCommitFactors49
import R1Z.ProverCommitArray49
/-! Exact line-factor cells and nested-array update primitives for the
circle weight constructor. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCircleRows49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSubtraction47 (one one_canonical one_decode)
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def matrix (rows : Nat → Nat → Old.Q) : Array (Array field.QM31 4#usize) 5#usize :=
  ProverCommitArray49.array 5#usize (fun i => ProverCommitQArray48.array 4#usize (rows i))

theorem matrix_update (rows : Nat → Nat → Old.Q) (d : Usize) (hd : d.val<5) (row : Nat → Old.Q) :
    Array.update (matrix rows) d (ProverCommitQArray48.array 4#usize row)=
      ok (matrix (Function.update rows d.val row)) := by
  rw [matrix,ProverCommitArray49.update 5#usize _ d hd]
  apply congrArg Result.ok
  unfold matrix
  congr 1
  funext i
  by_cases he : i=d.val
  · subst i;simp only [Function.update_self]
  · simp only [Function.update_of_ne he]

theorem zero_matrix : Array.repeat 5#usize (Array.repeat 4#usize field.QM31.ZERO)=matrix (fun _ _ => zero) := by
  rw [ProverCommitQArray48.repeat_zero]
  apply Subtype.ext
  simp only [Array.repeat,matrix,ProverCommitArray49.array,List.ofFn_const]

theorem line_exact (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ out : Nat → Old.Q, factors.line (ProverCommitNativeQ48.source x) (ProverCommitNativeQ48.source y)=
      ok (ProverCommitQArray48.array 4#usize out) ∧
      (∀ k, k<4 → Canonical (out k)) ∧
      ∀ k : Fin 4, decode (out k.val)=![1,decode x,decode y,decode x*decode y] k := by
  obtain ⟨xy,hxy,hcxy,hdxy⟩ := ProverCommitNativeQ48.mul x y hx hy
  refine ⟨ProverCommitFactors49.quad one x y xy,?_,?_,?_⟩
  · simp only [factors.line,hxy,bind_tc_ok,ProverCommitSampleTail49.source_one,ProverCommitFactors49.quad_array]
  · intro k hk
    exact ProverCommitFactors49.quad_canonical _ _ _ _ one_canonical hx hy hcxy k
  · intro k
    fin_cases k <;> simp [ProverCommitFactors49.quad,one_decode,hdxy]

#print axioms matrix_update
#print axioms zero_matrix
#print axioms line_exact
end R1Z.ProverCommitCircleRows49
