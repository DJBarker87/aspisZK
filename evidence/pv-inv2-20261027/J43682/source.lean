import R1Z.PV_Inv_DecodedSafety
import R1Z.PV_Inv_GlobalNative
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_DecodedNativeTests
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_MapGlobalStep PV_Inv_GlobalSafety
variable {W : Type} [Zero W] [DecidableEq W]

theorem tests_false (chi : Old.Q) (hc : Canonical chi)
    (banks : Banks QM31Exact) (t : Trace QM31Exact) (join : P_banks banks t) (lambda : QM31Exact)
    (weight : SourceLink QM31Exact → W) (registry : List (SourceLink QM31Exact)) (enumeration : P_registry registry)
    (es : List (Key × Entry Old.Q W))
    (entry_join : es.map (keyed decode)=entries banks lambda weight registry)
    (canon : ∀ e ∈ es, Canonical e.2.value)
    (s : State Key Old.Q W) (run : PV_Inv_GlobalSlots.run (empty zero) es=some s)
    (safe : NoPole t lambda (decode chi)) (key : Key) :
    PV_Inv_SourceTests.tests chi (PV_Inv_RawInvoke.reached (s key)) =
      ok (List.replicate (PV_Inv_RawInvoke.reached (s key)).length false) := by
  apply PV_Inv_SourceTests.all_false chi _ hc
  · intro v hv
    obtain ⟨e,he,_,hval⟩ := PV_Inv_GlobalOrigin.origin zero es s run key v hv
    rw [←hval]
    exact canon e he
  · intro v hv
    exact sub_ne_zero.mp (PV_Inv_DecodedSafety.reached_nonzero decode zero rfl banks t join lambda
      (decode chi) weight registry enumeration es entry_join s run safe key v hv)

#print axioms tests_false
end R1Z.PV_Inv_DecodedNativeTests
