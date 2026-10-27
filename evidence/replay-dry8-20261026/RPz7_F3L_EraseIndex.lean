import RPz7_F3J_InputRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_EraseIndex

theorem entry (Q : LiteralTranscript.Prefix) (row : Nat)
    (m : LiteralTranscript.Message) (c : LiteralTranscript.Challenge)
    (h : Q.rounds[row]?=some (m,c)) :
    (LiteralTranscript.erasePrefix Q).rounds[row]?=some (LiteralTranscript.erase m,c) := by
  simp only [LiteralTranscript.erasePrefix,List.getElem?_map,h,Option.map_some]

#print axioms entry
end AspisR1.F3L_EraseIndex
end
