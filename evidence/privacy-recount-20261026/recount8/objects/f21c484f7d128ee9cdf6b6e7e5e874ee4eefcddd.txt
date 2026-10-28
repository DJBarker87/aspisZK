import R0Z.JointView

/-! D12. G is pure: SemDecision.terminalValue reads only columns 0..15
and H1 (26); Mask.maskValue reads G with a point-only coefficient.
The product below is the binary vector-space direct sum, retaining every
raw coordinate, including overwritten and unused samples. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.Partition
open R0P R0Z.MaskLayout
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] {F : Subfield K}

abbrev ExtTape (F : Type) := Fin 1024 × Fin 4 → F
abbrev M (K : Type) [Field K] (F : Subfield K) :=
  (Fin 10 × Fin 1024 → F) × ExtTape F × ExtTape F
abbrev N (K : Type) [Field K] (F : Subfield K) :=
  ExtTape F × EligibleNoise K F
abbrev T (K : Type) [Field K] (F : Subfield K) := M K F × N K F

/-- Old extension slots are G, H1, D, in that order. -/
def aff : T K F →ₗ[F] AffTape K F where
  toFun t := Sum.elim t.1.1 (fun p =>
    if p.1 = 0 then t.1.2.1 p.2 else if p.1 = 1 then t.2.1 p.2 else t.1.2.2 p.2)
  map_add' p q := by
    funext c
    cases c with
    | inl p => rfl
    | inr p =>
      simp only [Pi.add_apply, Sum.elim_inr]
      split_ifs <;> rfl
  map_smul' a p := by
    funext c
    cases c with
    | inl p => rfl
    | inr p =>
      simp only [Pi.smul_apply, Sum.elim_inr]
      split_ifs <;> rfl


/-- A coordinate permutation, not a change of the honest tape law. -/
def equiv : T K F ≃ₗ[F] JointView.Tape K F where
  toFun t := (aff t, t.2.2)
  invFun t := ((fun p => t.1 (.inl p),
    (fun p => t.1 (.inr (0,p))), fun p => t.1 (.inr (2,p))),
    (fun p => t.1 (.inr (1,p))), t.2)
  left_inv t := by
    rcases t with ⟨⟨a,g,d⟩,h,e⟩
    rfl
  right_inv t := by
    refine Prod.ext ?_ rfl
    funext c
    cases c with
    | inl p => rfl
    | inr p =>
      rcases p with ⟨i,p⟩
      fin_cases i <;> rfl
  map_add' p q := Prod.ext (map_add aff p q) rfl
  map_smul' a p := Prod.ext (map_smul aff a p) rfl

def inlM : M K F →ₗ[F] T K F := LinearMap.inl F _ _
def inrN : N K F →ₗ[F] T K F := LinearMap.inr F _ _
def pureAff : M K F →ₗ[F] AffTape K F := aff.comp inlM
def pureTrace (B : PackBasis F) : M K F →ₗ[F] Trace K :=
  (traceLinear B).comp pureAff

attribute [local irreducible] copyInactiveRows

theorem extension_pure_zero (B : PackBasis F) (m : M K F) (s : Fin 1024) :
    extensionAff B 1 s (pureAff m) = 0 := by
  change (0 : K) + B.i * 0 + B.u * 0 + (B.i * B.u) * 0 = 0
  ring

/-- Keep the finite set abstract while proving evaluation of the zero family. -/
theorem balance_zero_generic {I : Type} [DecidableEq I] (S : Finset I)
    (d r : I) (f : I → AffTape K F →ₗ[F] K) (p : AffTape K F)
    (hz : ∀ s, f s p = 0) :
    (if r = d then -(∑ s ∈ S, f s) else f r) p = 0 := by
  by_cases hr : r = d
  · rw [if_pos hr, LinearMap.neg_apply, LinearMap.sum_apply]
    simp only [hz, Finset.sum_const_zero, neg_zero]
  · rw [if_neg hr]
    exact hz r

theorem padding_pure_zero (B : PackBasis F) (m : M K F) (r : Fin 1024) :
    balanceAff 0 (fun s => if CopyActiveRow s then 0 else extensionAff B 1 s) r
      (pureAff m) = 0 := by
  apply balance_zero_generic
  intro s
  by_cases hs : CopyActiveRow s
  · rw [if_pos hs]; rfl
  · rw [if_neg hs]; exact extension_pure_zero B m s

/-- Pure tape coordinates never change semantic cells or H1. -/
theorem pureTrace_fixed (B : PackBasis F) (m : M K F) (c : Fin 29)
    (hc : c.val < 16 ∨ c.val = 26) : pureTrace B m c = 0 := by
  funext r
  rcases hc with hc | hc
  · change (traceLinear B (pureAff m)) c r = 0
    simp only [traceLinear, LinearMap.pi_apply, if_pos hc, LinearMap.zero_apply]
  · have h16 : ¬c.val < 16 := by omega
    have h26 : ¬c.val < 26 := by omega
    change (traceLinear B (pureAff m)) c r = 0
    simp only [traceLinear, LinearMap.pi_apply, if_neg h16, dif_neg h26, if_pos hc]
    exact padding_pure_zero B m r

#print axioms equiv
#print axioms pureTrace_fixed
end R0Z.Partition
