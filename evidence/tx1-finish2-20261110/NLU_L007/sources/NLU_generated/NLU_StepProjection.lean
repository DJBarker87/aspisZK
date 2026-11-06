import NLU_EventProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
def eraseHead {H : Type} (r : Result (Post H)) : Result (NLC_Finish.Post H) := do
 let post ← r
 ok (erasePost post)
theorem step_projection {H : Type} (s : NLU.State H) :
 eraseHead (step s).reply=(PreparedHashCode.run (NLC_Finish.step s.machine)).2 := by
 unfold step
 cases h : PreparedHashCode.run (NLC_Finish.step s.machine) with
 | mk log reply =>
   cases reply with
   | fail err => rfl
   | div => rfl
   | ok post => change ok (erasePost (carry s post).2)=ok post;rw [carry_projection]
theorem step_digest {H : Type} (s : NLU.State H) :
 digestLog (step s).events=(PreparedHashCode.run (NLC_Finish.step s.machine)).1 := by
 unfold step
 cases h : PreparedHashCode.run (NLC_Finish.step s.machine) with
 | mk log reply =>
   cases reply with
   | fail err => exact (digest_append _ _).trans (by rw [entered_digest,map_digest];rfl)
   | div => exact (digest_append _ _).trans (by rw [entered_digest,map_digest];rfl)
   | ok post =>
     change digestLog ((entered s ++ log.map NLU.Event.digest) ++ (carry s post).1)=log
     rw [digest_append,digest_append,entered_digest,map_digest,carry_digest,List.nil_append,List.append_nil]
theorem step_input {H : Type} (s : NLU.State H) : (step s).input=s.machine.input := by
 unfold step
 cases h : PreparedHashCode.run (NLC_Finish.step s.machine) with
 | mk log reply => cases reply <;> rfl
#print axioms step_projection
#print axioms step_digest
#print axioms step_input
end AspisR1.NLU
end
