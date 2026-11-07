import NMX_R2_Heterogeneous
set_option autoImplicit false
namespace NMX_R2_HeterogeneousPrimitives
open RSL NMX_R2_RawChildren NMX_R2_Heterogeneous

theorem map_identity {A : Type} (o : Obs (Except ProgramError A)) : mapObs id o = o := by
 cases o with
 | mk exit events =>
   cases exit with
   | ret reply => cases reply <;> rfl
   | abort => rfl
   | diverge => rfl

theorem refl {A : Type} (m : RS A) : NMX_R2_Heterogeneous.Refines id m m := by
 intro env o h
 rw [map_identity]
 exact h

theorem pure {A B : Type} (encode : A → B) (a : A) :
 NMX_R2_Heterogeneous.Refines encode (RS.pure a) (RS.pure (encode a)) := by
 intro env o h
 unfold RS.pure Spec.pure at h
 subst o
 rfl

theorem allocation {A B : Type} (encode : A → B) (a : A) :
 NMX_R2_Heterogeneous.Refines encode
  (RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure a))
  (RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure (encode a))) := by
 apply NMX_R2_Heterogeneous.bind id encode _ _ _ _ (refl _)
 intro unit
 exact pure encode a
#print axioms map_identity
#print axioms refl
#print axioms pure
#print axioms allocation
end NMX_R2_HeterogeneousPrimitives
