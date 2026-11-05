import NID_ResumeCanonical
set_option autoImplicit false
noncomputable section
namespace NID_ResumeFields
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NID_ResumeCanonical
open CheckpointBytes4ReaderFields CheckpointBytes4Layout

structure Domain (p : verifier.Prepared) (a : verifier.Accumulator) : Prop where
 variant : p.variant=.S2
 gamma : ECanonical p.gamma
 kappa : ECanonical p.kappa
 alpha : ∀ x ∈ p.alpha.val, ECanonical x
 rho : KCanonical p.rho
 semantic : ∀ x ∈ p.semantic_alpha.val, KCanonical x
 coordinates : ∀ z ∈ p.z.val, KCanonical z.x ∧ KCanonical z.y
 claim : ECanonical p.claim
 rhs : ECanonical a.rhs
 power : KCanonical a.power
 width : a.weights.val.length=64
 weights : ∀ x ∈ a.weights.val, KCanonical x

/-- Domains are derived from the SAME successful returned pair and actual flat
reader provenance. No canonical field, allocation success or acceptance input. -/
theorem returned (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a : verifier.Accumulator)
 (size : ck.val.length=1768)
 (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D ck proof pub .S2 hash=ok (.Ok (p,a))) :
 Domain p a := by
 obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof pub .S2 hash p a success
 have flat := flat_fields reserved ck p a f size
 obtain ⟨wm,_,wvalue⟩ := flat.weights
 obtain ⟨sm,_,svalue⟩ := flat.semantic
 refine ⟨f.variant,e_at _ _ _ flat.gamma,e_at _ _ _ flat.kappa,?_,
  k_at _ _ _ flat.rho,?_,?_,e_at _ _ _ flat.claim,e_at _ _ _ flat.rhs,
  k_at _ _ _ flat.power,?_,?_⟩
 · rw [f.alpha]
   intro x hx
   have hx' : x=f.alpha0 ∨ x=f.alpha1 := by simpa using hx
   rcases hx' with rfl | rfl
   · exact e_at _ _ _ flat.alpha0
   · exact e_at _ _ _ flat.alpha1
 · rw [svalue]
   intro x hx
   obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
   exact sourceK_canonical v
 · rw [f.coordinates]
   intro z hz
   have hz' : z=⟨f.x0,f.y0⟩ ∨ z=⟨f.x1,f.y1⟩ := by simpa using hz
   rcases hz' with rfl | rfl
   · exact ⟨k_at _ _ _ flat.x0,k_at _ _ _ flat.y0⟩
   · exact ⟨k_at _ _ _ flat.x1,k_at _ _ _ flat.y1⟩
 · rw [wvalue]
   simp
 · rw [wvalue]
   intro x hx
   obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
   exact sourceK_canonical v
#print axioms returned
end NID_ResumeFields
