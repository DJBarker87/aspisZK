import R1Z.PV_Inv_GlobalNative
import R1Z.PV_Inv_Scan
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GlobalScan
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_GlobalSafety
local instance : DecidableEq U32 := Classical.decEq _

theorem native_guarded {I : Type} [DecidableEq I] (chi : Old.Q) (hc : Canonical chi)
    (es : List (I × Entry Old.Q U32)) (s : State I Old.Q U32)
    (canon : ∀ e ∈ es, Canonical e.2.value)
    (guard : PV_Inv_Scan.scan (decode chi) true (es.map (fun e => decode e.2.value))=true)
    (hr : PV_Inv_GlobalSlots.run (empty zero) es=some s) (key : I) :
    PV_Inv_SourceTests.tests chi (PV_Inv_RawInvoke.reached (s key))=
      ok (List.replicate (PV_Inv_RawInvoke.reached (s key)).length false) := by
  apply PV_Inv_GlobalNative.all_reached_tests chi hc es s canon _ hr key
  intro e he
  exact ((PV_Inv_Scan.scan_iff (decode chi) true _).mp guard).2 _ (List.mem_map.mpr ⟨e,he,rfl⟩)

#print axioms native_guarded
end R1Z.PV_Inv_GlobalScan
