import NFM_Control
set_option autoImplicit false
namespace AspisR1.NFM_Span

/-- The actual wrapper's slot range establishes the complete scalar slice
bound, including the short last batch. -/
theorem scalar (slot : Fin 4) (term : Fin 26) :
    slot.val*120+term.val*4+4≤464 ∧
    slot.val*120+term.val*4+4≤608 := by
  have hs:=slot.isLt
  have ht:=term.isLt
  omega

theorem tail (slot : Fin 4) :
    slot.val*120+104+16≤480 ∧
    480+slot.val*32+16≤608 ∧
    480+slot.val*32+16+16≤608 := by
  have hs:=slot.isLt
  omega

/-- A position supplies both the coefficient and slice endpoints used by the
native per-window body, with no data-dependent iterator state. -/
theorem window (k : Fin 7) :
    4*k.val<26 ∧ min (4*k.val+4) 26≤26 ∧
    min (4*k.val+4) 26-4*k.val≤4 := by
  have hk:=k.isLt
  omega

#print axioms scalar
#print axioms tail
#print axioms window
end AspisR1.NFM_Span
