import R1Z.ProverCommitCircleFill49
/-! Source-owned five-row circle factor constructor, including initialization. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCircleOutput49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitCircleRows49
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open AspisCircleTensorBinding

def model (x y : QM31Exact) (d : Nat) (k : Fin 4) : QM31Exact :=
  if d=0 then ![1,y,x,x*y] k else ProverCommitCircleFill49.model x d k

attribute [local irreducible] matrix ProverCommitQArray48.array ProverCommitNativeQ48.source

theorem rows_exact (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ rows : Nat → Nat → Old.Q,
      factors.circle_rows (ProverCommitNativeQ48.source x) (ProverCommitNativeQ48.source y)=ok (matrix rows) ∧
      (∀ d k, d<5 → k<4 → Canonical (rows d k)) ∧
      ∀ d : Fin 5, ∀ k : Fin 4, decode (rows d.val k.val)=model (decode x) (decode y) d.val k := by
  obtain ⟨first,hfirst,hcfirst,hdfirst⟩ := ProverCommitFactors49.circle_exact x y hx hy
  let initial : Nat → Nat → Old.Q := Function.update (fun _ _ => zero) 0 first
  have hcinit : ∀ d k, d<5 → k<4 → Canonical (initial d k) := by
    intro d k hd hk
    by_cases he : d=0
    · subst d;simpa only [initial,Function.update_self] using hcfirst k hk
    · simpa only [initial,Function.update_of_ne he] using zero_canonical
  obtain ⟨next,hnext,hcnext,hdnext⟩ := ProverCommitFactors49.double_exact x hx
  obtain ⟨rows,hrows,hcrows,hdrows⟩ := ProverCommitCircleFill49.fill_value (decode x) initial hcinit
    4 1#usize 4#u8 rfl (by decide) (by decide) next hcnext (by simpa using hdnext)
  refine ⟨rows,?_,hcrows,?_⟩
  · rw [factors.circle_rows,zero_matrix]
    simp only [hfirst,bind_tc_ok]
    rw [matrix_update _ 0#usize (by decide) first]
    simp only [hnext,bind_tc_ok,show (0#usize).val=0 from rfl]
    exact hrows
  · intro d k
    rw [hdrows]
    simp only [show (1#usize).val=1 from rfl]
    by_cases he : d.val=0
    · rw [if_neg (by omega),model,if_pos he]
      simp only [initial,he,Function.update_self,hdfirst]
    · rw [if_pos (by have := d.isLt;omega),model,if_neg he]

#print axioms rows_exact
end R1Z.ProverCommitCircleOutput49
