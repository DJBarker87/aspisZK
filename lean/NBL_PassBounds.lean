import NBL_PassConstruct
set_option autoImplicit false
namespace AspisR1.NBL_PassBounds
open SamplerMachineBounds

theorem remainder {r out : UInt64} {xs qs : List UInt32}
    (tr : LPk_Induction.Pass r xs out qs) (good : r.toNat<P) : out.toNat<P := by
  induction tr with
  | nil r => exact good
  | cons step tail ih => exact ih step.2

/-- Each actual digit comes from the SAME pass's final bounded remainder. -/
theorem canonical {n : Nat} {xs out : List UInt32} {ds : List Nat}
    (tr : LPk_Induction.Digits n xs ds out) : ∀ d∈ds,d<P := by
  induction tr with
  | nil xs => intro d h;cases h
  | cons first tail ih =>
    intro d member
    rcases List.mem_cons.mp member with rfl | rest
    · exact remainder first P_pos
    · exact ih d rest

#print axioms remainder
#print axioms canonical
end AspisR1.NBL_PassBounds
