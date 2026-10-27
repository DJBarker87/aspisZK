import R1Z.PV_Inv_RawNative
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_RawCanonical
open Aeneas Aeneas.Std
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawInvoke
local instance : DecidableEq U32 := Classical.decEq _

theorem reached_canonical (es : List (Entry Old.Q U32)) (s : Slots Old.Q U32)
    (canon : ∀ e ∈ es, Canonical e.value) (hr : run (empty zero) es=some s) :
    ∀ x ∈ reached s, Canonical x := by
  have h := preserves Canonical es (empty zero) s (empty_good _ zero) canon hr
  exact reached_good Canonical s h

#print axioms reached_canonical
end R1Z.PV_Inv_RawCanonical
