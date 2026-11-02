import NEI_WideCtorLaw
set_option autoImplicit false
noncomputable section
namespace NEI_WideConstruction
open Aeneas Aeneas.Std Result
abbrev value := NEI_WideCtorLaw.value
theorem source (a b c d e f g h : U32)
 (ha : a.val<2147483647) (hb : b.val<2147483647)
 (hc : c.val<2147483647) (hd : d.val<2147483647)
 (he : e.val<2147483647) (hf : f.val<2147483647)
 (hg : g.val<2147483647) (hh : h.val<2147483647) :
 FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
 (Array.make 8#usize [a,b,c,d,e,f,g,h]) = ok (some (value a b c d e f g h)) := by
 rw [NEI_WideCtorLaw.limbs_result]
 have canon : a<2147483647#u32 ∧ b<2147483647#u32 ∧ c<2147483647#u32 ∧ d<2147483647#u32 ∧
  e<2147483647#u32 ∧ f<2147483647#u32 ∧ g<2147483647#u32 ∧ h<2147483647#u32 := by scalar_tac
 simp only [if_pos canon]
#print axioms source
end NEI_WideConstruction
end
