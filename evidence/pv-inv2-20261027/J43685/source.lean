import R1Z.PV_Inv_DecodedNativeTests
import R1Z.PV_Inv_PreGuard
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardedNativeTests
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_MapGlobalStep PV_Inv_GlobalSafety
variable {W : Type} [Zero W] [DecidableEq W]

theorem tests_false (chi : Old.Q) (hc : Canonical chi)
    (banks : Banks QM31Exact) (t : Trace QM31Exact) (join : P_banks banks t) (lambda : QM31Exact)
    (weight : SourceLink QM31Exact → W) (registry : List (SourceLink QM31Exact)) (enumeration : P_registry registry)
    (es : List (Key × Entry Old.Q W))
    (entry_join : es.map (keyed decode)=entries banks lambda weight registry)
    (canon : ∀ e ∈ es, Canonical e.2.value)
    (s : State Key Old.Q W) (run : PV_Inv_GlobalSlots.run (empty zero) es=some s)
    (nativeGuard : Bool) (P_guard_equation : nativeGuard=PV_Inv_PreGuard.noPoleRef t lambda (decode chi))
    (helper_called : nativeGuard=true) (key : Key) :
    PV_Inv_SourceTests.tests chi (PV_Inv_RawInvoke.reached (s key)) =
      ok (List.replicate (PV_Inv_RawInvoke.reached (s key)).length false) := by
  have safe := (PV_Inv_PreGuard.source_equation t lambda (decode chi)).mp
    (P_guard_equation.symm.trans helper_called)
  exact PV_Inv_DecodedNativeTests.tests_false chi hc banks t join lambda weight registry enumeration es entry_join canon s run safe key

#print axioms tests_false
end R1Z.PV_Inv_GuardedNativeTests
