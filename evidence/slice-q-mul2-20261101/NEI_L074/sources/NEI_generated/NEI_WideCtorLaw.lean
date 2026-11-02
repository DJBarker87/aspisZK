import NEG_DotAssociation
set_option autoImplicit false
noncomputable section
namespace NEI_WideCtorLaw
open Aeneas Aeneas.Std Result
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact
def value (a b c d e f g h : U32) : E := ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
theorem limbs_result (a b c d e f g h : U32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
      ok (if a < 2147483647#u32 ∧ b < 2147483647#u32 ∧ c < 2147483647#u32 ∧
        d < 2147483647#u32 ∧ e < 2147483647#u32 ∧ f < 2147483647#u32 ∧
        g < 2147483647#u32 ∧ h < 2147483647#u32
        then some (value a b c d e f g h) else none) := by
  simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    Array.index_usize,Array.make,FIo_Native.aspis_core.field.P,value]
  repeat' split
  all_goals simp_all <;> omega


/-- Observe the complete Option discriminant and all eight result coordinates. -/
def observe (input : Array U32 8#usize) : Result (Option (Array U32 8#usize)) := do
 let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs input
 match out with
 | none => ok none
 | some value => do
   let words ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value
   ok (some words)

theorem complete (a b c d e f g h : U32) :
 observe (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
 ok (if a<2147483647#u32 ∧ b<2147483647#u32 ∧ c<2147483647#u32 ∧ d<2147483647#u32 ∧
        e<2147483647#u32 ∧ f<2147483647#u32 ∧ g<2147483647#u32 ∧ h<2147483647#u32
     then some (Array.make 8#usize [a,b,c,d,e,f,g,h]) else none) := by
 unfold observe
 rw [limbs_result]
 simp only [bind_tc_ok]
 by_cases valid : a<2147483647#u32 ∧ b<2147483647#u32 ∧ c<2147483647#u32 ∧ d<2147483647#u32 ∧
   e<2147483647#u32 ∧ f<2147483647#u32 ∧ g<2147483647#u32 ∧ h<2147483647#u32
 · simp only [if_pos valid]
   rfl
 · simp only [if_neg valid]
   rfl
#print axioms limbs_result
#print axioms complete
end NEI_WideCtorLaw
end
