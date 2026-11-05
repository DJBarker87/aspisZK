import NHG_COMBINED_IMPORT
import NBN_WordArrayEq
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionWords
attribute [local instance] Classical.propDecidable

/-- Both extracted M31 carriers are raw U32 words; transport the comparator
without assuming canonicality or equality of the source frontiers. -/
theorem comparator :
 FIq_Native.field.M31.Insts.CoreCmpPartialEqM31=
 AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 := rfl

theorem equal {n : Usize} (a b : Array U32 n) :
 core.array.equality.PartialEqArray.eq FIq_Native.field.M31.Insts.CoreCmpPartialEqM31 a b=
 ok (decide (a=b)) := by
 rw [comparator]
 exact NBN_WordArrayEq.source a b

#print axioms comparator
#print axioms equal
end AspisR1.NHU_TransitionWords
end
