import NMX_R6_Observation
set_option autoImplicit false
namespace NMX_R7_LiftMember
open RSL NMX_R6_Observation NMS_R2N_Interpreted

theorem fusion {A B : Type} (o : Obs A) (k : A → Obs (Except ProgramError B)) :
 rsbind (mapObs Except.ok o) k = bind o k := by
 cases o with
 | mk exit events => cases exit <;> rfl

theorem member {A B : Type} (m : Spec A) (next : A → RS B) (env : Env)
 (o : Obs A) (k : A → Obs (Except ProgramError B))
 (hm : m env o) (hk : ∀ a, next a env (k a)) :
 RS.bind (RS.lift m) next env (bind o k) := by
 rw [←fusion]
 exact rsmember _ next env _ k (LIBB_ModelGraph.mapped_member _ _ env o hm) hk
#print axioms fusion
#print axioms member
end NMX_R7_LiftMember
