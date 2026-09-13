import AspisV8H1C2.FiniteTransport
set_option autoImplicit false
namespace AspisV8R12
noncomputable section
variable {Raw S : Type*} {Values Noise : S → Type*}
def skeletonValueEquiv (e : ∀ s, Noise s → Values s ≃ Values s) :
    (Σ s, Values s × Noise s) ≃ (Σ s, Values s × Noise s) where
  toFun x := ⟨x.1, e x.1 x.2.2 x.2.1, x.2.2⟩
  invFun y := ⟨y.1, (e y.1 y.2.2).symm y.2.1, y.2.2⟩
  left_inv x := by rcases x with ⟨s,v,n⟩; simp
  right_inv y := by rcases y with ⟨s,v,n⟩; simp
def rawSkeletonTransport (codec : Raw ≃ (Σ s, Values s × Noise s))
    (e : ∀ s, Noise s → Values s ≃ Values s) : Raw ≃ Raw :=
  codec.trans ((skeletonValueEquiv e).trans codec.symm)
theorem raw_skeleton_transport_uniform [Fintype Raw] [Nonempty Raw]
    (codec : Raw ≃ (Σ s, Values s × Noise s)) (e : ∀ s, Noise s → Values s ≃ Values s) :
    AspisV8H1C2.SameUniformLaw (rawSkeletonTransport codec e) (fun raw : Raw => raw) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _ (rawSkeletonTransport codec e) (fun _ => rfl)
#print axioms skeletonValueEquiv
#print axioms raw_skeleton_transport_uniform
end
end AspisV8R12
