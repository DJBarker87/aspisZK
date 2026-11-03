import NBG_WideCarriers
set_option autoImplicit false
noncomputable section
namespace NEI_WideCtorLaw
open Aeneas Aeneas.Std Result
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact
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
 rw [NBG_WideCarriers.limbs_result]
 simp only [bind_tc_ok]
 split <;> rfl
#print axioms complete
end NEI_WideCtorLaw
end
