import AspisV8R19.R662FullIndexedMaskPreservation
import AspisV8R19.R664FullMomentP2
set_option autoImplicit false
namespace AspisV8R19.R665FullSourceP2Boundary
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R660FullSourceResidualCorrection R662FullIndexedMaskPreservation R664FullMomentP2
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem full_flatten_low_slot (q : Index 256 → F) (d : Fin 256) (s : Fin 4) :
    flattenFull q (4*d.val+s.val) = q (d,s) := by
  rw [flattenFull,dif_pos (by omega : 4*d.val+s.val<1024)]
  congr 1
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

/-- Exact full 1024-coordinate source pairing, retaining every image-tail
weight and without any low-support hypothesis on the incoming quotient. -/
theorem full_flatten_pairing (q : Index 256 → F) (w : Nat → F) :
    rangeDot 1024 w (flattenFull q) =
      ∑ d : Fin 256, ∑ s : Fin 4, q (d,s)*w (4*d.val+s.val) := by
  unfold rangeDot
  rw [show (1024:Nat)=4*256 by decide,CircleChannelsBridge.sum_quads,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro d _
  have h0 := full_flatten_low_slot q d (0:Fin 4)
  have h1 := full_flatten_low_slot q d (1:Fin 4)
  have h2 := full_flatten_low_slot q d (2:Fin 4)
  have h3 := full_flatten_low_slot q d (3:Fin 4)
  simp at h0 h1 h2 h3
  simp [Fin.sum_univ_succ,h0,h1,h2,h3]
  ring

/-- The complete all-beta relation implies the exact full source p2 channel
moment difference, including the actual tau image updates. This is source
field algebra; it does not bind the native callback or legal witnesses. -/
theorem full_source_p2 (half quarter a b c kappa tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (r g : Index 256 → F)
    (hquarter : quarter ≠ 0) (hscale : scale ≠ 0)
    (hquad : ∀ beta : F, ∀ k : Fin 7,
      coefficient (sourceKernel 256 k.val quarter)
        (fun i => (1-beta)*r i+scale*beta*g i)
        (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i+
          beta*fullWeight half a b c kappa tau z previous true i)=0) :
    scale * (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull g) -
      rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull g)) -
      (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull r) -
      rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull r)) = 0 := by
  simp only [full_flatten_pairing]
  exact full_moment_p2 256 quarter scale hquarter hscale r g
    (fullWeight half a b c kappa tau z previous false)
    (fullWeight half a b c kappa tau z previous true) hquad

#print axioms full_flatten_low_slot
#print axioms full_flatten_pairing
#print axioms full_source_p2
end
end AspisV8R19.R665FullSourceP2Boundary
