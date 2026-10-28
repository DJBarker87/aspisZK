import NDO_JGr_Geometry
import RPz7_SAP_PrepareOwner
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_PreparedFields
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

theorem source (p : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch)) :
    Port5Q2_Prepared.PreparedFields (Tx1Q_Carriers.prepared p) := by
  have owner := SAP_PrepareOwner.installed
    (Op3I_Install.install (Op4P_Install.install
      (WAdm_Execution.base (JGp_Allocation.base (Op5T_Concrete.current JGp_Seeds.base)) true
        (SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query))
        (SAQ_Constructor.install () JGp_Seeds.geometry))))
    JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
  rw [JGe_Boundaries.circle] at owner
  exact owner.accepted digest () _ JFx_NativeBytes.proof JGp_TX1Initial.zero p scratch prepare
#print axioms source
end AspisR1.JHe_PreparedFields
end
