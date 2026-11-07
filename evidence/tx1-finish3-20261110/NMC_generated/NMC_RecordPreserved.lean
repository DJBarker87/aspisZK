import NMC_RecordWrites
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Records
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem preserve25 {H : Type} (s after : NLC_Finish.State H) (major : Major s)
 (origin : Origin s 25#u8 s.locals.record25)
 (notFirst : s.next≠.record25a) (notSecond : s.next≠.record25b)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 Origin after 25#u8 after.locals.record25 := by
 have frames:=NMC_Slots.source_frame s after major head
 rcases frames with ⟨f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22⟩
 have same:=f18 ⟨notFirst,notSecond⟩
 have input:=NLC_Finish.source_input_frame s after head
 change after.input=s.input at input
 intro record stored
 rw [same] at stored
 simpa only [input] using origin record stored
#print axioms preserve25
theorem preserve26 {H : Type} (s after : NLC_Finish.State H) (major : Major s)
 (origin : Origin s 26#u8 s.locals.record26)
 (notFirst : s.next≠.record26a) (notSecond : s.next≠.record26b)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 Origin after 26#u8 after.locals.record26 := by
 have frames:=NMC_Slots.source_frame s after major head
 rcases frames with ⟨f0,f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22⟩
 have same:=f19 ⟨notFirst,notSecond⟩
 have input:=NLC_Finish.source_input_frame s after head
 change after.input=s.input at input
 intro record stored
 rw [same] at stored
 simpa only [input] using origin record stored
#print axioms preserve26
/-- The same source result is preserved separately for repeated25/26
occurrences. It is an internal invariant, not a permitted row-root premise. -/
theorem reachable {H : Type} (input : NLU.Input H) (s : NLU.State H)
 (reached : NLU.Reachable input s) :
 Origin s.machine 25#u8 s.machine.locals.record25 ∧ Origin s.machine 26#u8 s.machine.locals.record26 := by
 induction reached with
 | initial=>constructor <;> intro record stored <;> cases stored
 | @next before after reached head ih=>
   have actual:=(NLU.next_characterization before after head).1
   have major:=(NLU.reachable_invariant input before reached).1.2.1
   constructor
   · by_cases a : before.machine.next=.record25a
     · exact record25a before.machine after.machine a actual
     · by_cases b : before.machine.next=.record25b
       · exact record25b before.machine after.machine b actual
       · exact preserve25 before.machine after.machine major ih.1 a b actual
   · by_cases a : before.machine.next=.record26a
     · exact record26a before.machine after.machine a actual
     · by_cases b : before.machine.next=.record26b
       · exact record26b before.machine after.machine b actual
       · exact preserve26 before.machine after.machine major ih.2 a b actual
#print axioms reachable
set_option pp.proofs false in #print reachable
end AspisR1.NMC_Records
end
