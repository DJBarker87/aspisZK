import R1Z.PV_Inv_RawCanonical
import R1Z.PV_Inv_SourceTests
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativePackedTests
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawInvoke
local instance : DecidableEq U32 := Classical.decEq _

theorem packing_tests (chi : Old.Q) (hc : Canonical chi) (es : List (Entry Old.Q U32))
    (s : Slots Old.Q U32) (canon : ∀ e ∈ es, Canonical e.value)
    (safe : ∀ e ∈ es, decode chi ≠ decode e.value) (hr : run (empty zero) es=some s) :
    PV_Inv_SourceTests.tests chi (reached s)=ok (List.replicate (reached s).length false) := by
  apply PV_Inv_SourceTests.all_false chi (reached s) hc
  · exact PV_Inv_RawCanonical.reached_canonical es s canon hr
  · apply reached_good
    exact preserves (fun x => decode chi ≠ decode x) es (empty zero) s
      (empty_good _ zero) safe hr

#print axioms packing_tests
end R1Z.PV_Inv_NativePackedTests
