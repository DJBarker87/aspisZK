import NHG_COMBINED_IMPORT
import NBH_ArrayEq
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionHeaderPrelude
attribute [local instance] Classical.propDecidable

theorem bytes {n : Usize} (a b : Array U8 n) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b=ok (decide (a≠b)) := by
 simp only [core.array.equality.PartialEqArray.ne,NBH_ArrayEq.source,bind_tc_ok]
 by_cases h : a=b <;> simp [h]

theorem option (a b : Option U64) :
 ∃ out,core.cmp.PartialEq.ne.trait_default
 (FIq_Native.core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) a b=ok out := by
 cases a <;> cases b <;> exact ⟨_,rfl⟩
#print axioms bytes
#print axioms option
end AspisR1.NHU_TransitionHeaderPrelude
end
