import NHU_TransitionWords
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionNe
attribute [local instance] Classical.propDecidable

theorem result {n : Usize} (a b : Array U32 n) :
 core.array.equality.PartialEqArray.ne FIq_Native.field.M31.Insts.CoreCmpPartialEqM31 a b=
 ok (decide (a≠b)) := by
 simp only [core.array.equality.PartialEqArray.ne,core.cmp.PartialEq.ne.trait_default,
  NHU_TransitionWords.equal,bind_tc_ok]
 by_cases h : a=b <;> simp [h]

#print axioms result
end AspisR1.NHU_TransitionNe
end
