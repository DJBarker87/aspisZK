import Mathlib

/-! Symbolic dimension argument for an injective map between kernels.
No dimension or finite universe is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.KernelImage

variable {k V W : Type} [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- If g is onto W, its kernel has the smallest possible dimension among
kernels of maps V → W. An injection from another such kernel is therefore onto. -/
theorem surjective (f g : V →ₗ[k] W) (hg : Function.Surjective g)
    (c : LinearMap.ker f →ₗ[k] LinearMap.ker g) (hc : Function.Injective c) :
    Function.Surjective c := by
  have hf := f.finrank_range_add_finrank_ker
  have hg' := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at hg'
  have hr := (LinearMap.range f).finrank_le
  have hi := LinearMap.finrank_le_finrank_of_injective hc
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := c) ?_).mp hc
  omega

#print axioms surjective
end R0Z.KernelImage
