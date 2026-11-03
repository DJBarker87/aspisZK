import NET_CallerWindows
set_option autoImplicit false
namespace NET_WindowEmbedding
open Aeneas Aeneas.Std Result

def backing (part : List U8) (offset total : Nat) : List U8 :=
 List.replicate offset 0#u8 ++ part ++ List.replicate (total-offset-part.length) 0#u8

theorem length (part : List U8) (offset total : Nat)
 (bound : offset+part.length≤total) : (backing part offset total).length=total := by
 simp only [backing,List.length_append,List.length_replicate]
 omega

/-- Every raw parser input occurs in a full backing allocation; suffix/prefix
bytes add no restriction on its value. No concrete 608-cell term is reduced. -/
theorem selected (part : List U8) (offset total : Nat) :
 ((backing part offset total).drop offset).take part.length=part := by
 simp [backing,List.drop_append,List.take_append]

/-- This is a data embedding, not a pointer-provenance theorem. The native
checks supply the actual live allocation and same borrowed place separately. -/
theorem native_window (part : List U8) (offset total : Nat)
 (bound : offset+part.length≤total) :
 ∃ raw : List U8, raw.length=total ∧ (raw.drop offset).take part.length=part :=
 ⟨backing part offset total,length part offset total bound,selected part offset total⟩

#print axioms length
#print axioms selected
#print axioms native_window
end NET_WindowEmbedding
