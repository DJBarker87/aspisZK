import NNG_Reached137
import NNG_Representation136
import NNG_Context137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishInput137
open Aeneas Aeneas.Std NMP_prepare NMP_Transport

theorem observer (obs : RSL.Observer) : NNG_FinishAdapter137.observer (NNG_Context137.observer obs)=
    NNG_Representation136.observer obs := by
  cases obs <;> rfl
#print axioms observer

theorem input (env : RSL.Env) (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : RSL.Observer) :
    NNG_FinishAdapter137.childInput (NNG_PublicSource137.digest env) pub (LIB_VCarriers.prefixRaw p) t
      (LIB_VCarriers.challengesRaw c) (NNG_Context137.observer obs) =
      NNG_Representation136.input ⟨pub,p,t,c⟩ obs env := by
  have ch := congrArg NNG_Transport.fromT3 (NNG_LIBTerminal.lower_challenges c)
  simp only [NNG_Transport.toT3_inverse] at ch
  unfold NNG_FinishAdapter137.childInput NNG_Representation136.input NNG_ConcreteInput136.input
  rw [←ch,observer]
  rfl
#print axioms input
end AspisR1.NNG_FinishInput137
