import NMO_BlindStored
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ArrayStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem low_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (before : LowCanonical s) (notWriter : s.next≠.lowArray)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : LowCanonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro value stored
 rw [frame.2.2.2.2.2.2.1 notWriter] at stored
 exact before value stored
#print axioms low_preserved
theorem high_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (before : HighCanonical s) (notWriter : s.next≠.highArray)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : HighCanonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro value stored
 rw [frame.2.2.2.2.2.2.2.1 notWriter] at stored
 exact before value stored
#print axioms high_preserved
theorem blind_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (before : BlindCanonical s) (notWriter : s.next≠.blind)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : BlindCanonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro value stored
 rw [frame.2.2.2.2.2.2.2.2.1 notWriter] at stored
 exact before value stored
#print axioms blind_preserved
/-- Canonical mask-array and blind domains are derived along the initialized
source chain, rather than supplied as premises about child outputs. -/
theorem reachable {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) :
 LowCanonical s.machine ∧ HighCanonical s.machine ∧ BlindCanonical s.machine := by
 induction reached with
 | initial=>constructor
            · intro value stored;cases stored
            · constructor <;> intro value stored <;> cases stored
 | @next before after reached head ih=>
  have actual:=(NLU.next_characterization before after head).1
  have major:=(NLU.reachable_invariant input before reached).1.2.1
  constructor
  · by_cases site : before.machine.next=.lowArray
    · exact low_written input domain before reached site after.machine actual
    · exact low_preserved before.machine after.machine major ih.1 site actual
  · constructor
    · by_cases site : before.machine.next=.highArray
      · exact high_written input domain before reached site after.machine actual
      · exact high_preserved before.machine after.machine major ih.2.1 site actual
    · by_cases site : before.machine.next=.blind
      · exact blind_written input domain before reached site after.machine actual
      · exact blind_preserved before.machine after.machine major ih.2.2 site actual
#print axioms reachable
set_option pp.proofs false in #print reachable
end AspisR1.NMO_ArrayStored
end
