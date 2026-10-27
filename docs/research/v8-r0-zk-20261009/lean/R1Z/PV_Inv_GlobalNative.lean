import R1Z.PV_Inv_GlobalOrigin
import R1Z.PV_Inv_RawU32
import R1Z.PV_Inv_SourceTests
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GlobalNative
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_GlobalSafety
local instance : DecidableEq U32 := Classical.decEq _

theorem all_reached_tests {I : Type} [DecidableEq I] (chi : Old.Q) (hc : Canonical chi)
    (es : List (I × Entry Old.Q U32)) (s : State I Old.Q U32)
    (canon : ∀ e ∈ es, Canonical e.2.value)
    (safe : ∀ e ∈ es, decode chi ≠ decode e.2.value)
    (hr : PV_Inv_GlobalSlots.run (empty zero) es=some s) (key : I) :
    PV_Inv_SourceTests.tests chi (PV_Inv_RawInvoke.reached (s key))=
      ok (List.replicate (PV_Inv_RawInvoke.reached (s key)).length false) := by
  apply PV_Inv_SourceTests.all_false chi _ hc
  · intro x hx
    obtain ⟨e,he,_,hval⟩ := PV_Inv_GlobalOrigin.origin zero es s hr key x hx
    rw [←hval]
    exact canon e he
  · intro x hx
    obtain ⟨e,he,_,hval⟩ := PV_Inv_GlobalOrigin.origin zero es s hr key x hx
    rw [←hval]
    exact safe e he

#print axioms all_reached_tests
end R1Z.PV_Inv_GlobalNative
