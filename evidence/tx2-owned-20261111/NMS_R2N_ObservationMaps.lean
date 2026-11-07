import NMS_R2N_Interpreted
set_option autoImplicit false
namespace NMS_R2N_ObservationMaps
open RSL NMS_R2N_Interpreted

theorem identity {A : Type} (o : Obs A) : mapObs id o = o := by
 cases o with
 | mk exit events => cases exit <;> rfl

/-- Full observation transport through an invertible carrier map; abort and
divergence prefixes are preserved without any post-stop value. -/
theorem cancel {A B : Type} (encode : A → B) (decode : B → A)
 (inverse : ∀ a, decode (encode a) = a) (meaning : Spec A) :
 Simulates decode (Spec.map encode meaning) meaning := by
 intro env observation run
 rcases run with ⟨a,events,o2,first,last,same⟩ | ⟨events,first,same⟩ | ⟨events,first,same⟩
 · subst o2
   subst observation
   simpa only [mapObs,mapExit,inverse,List.append_nil] using first
 · subst observation
   exact first
 · subst observation
   exact first
#print axioms identity
#print axioms cancel
end NMS_R2N_ObservationMaps
