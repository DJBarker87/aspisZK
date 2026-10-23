import R1Z.ProverCommitPointRows49
/-! Whole five-row point-factor initializer, with exact stored row identities. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPointRowsOutput49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitCircleRows49 ProverCommitPointRows49

theorem all (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i)) :
    ∃ out : Nat → Nat → Old.Q,
      point_rows.all (ProverCommitQArray48.array 10#usize p)=ok (matrix out) ∧
      (∀ i k, i<5 → k<4 → Canonical (out i k)) ∧
      ∀ i : Fin 5, out i.val=target p hp i.val := by
  obtain ⟨out,hout,hcout,heq⟩ := fill p hp 5 (fun _ _ => zero) (fun _ _ _ _ => zero_canonical)
    0#usize 5#u8 rfl (by decide)
  refine ⟨out,?_,hcout,?_⟩
  · simp only [point_rows.all,zero_matrix,hout]
  · intro i
    rw [heq,if_pos (by have := i.isLt;change 0 ≤ i.val ∧ i.val<0+5;omega)]

#print axioms all
end R1Z.ProverCommitPointRowsOutput49
