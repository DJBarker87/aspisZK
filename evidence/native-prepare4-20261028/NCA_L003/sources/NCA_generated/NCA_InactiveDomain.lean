import NCA_InactiveModel
import NBA_WideView
set_option autoImplicit false
namespace AspisR1.NCA_InactiveDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- The same returned wide view establishes the canonical input domain of
NCA_K004. The complete installed serializer Result then follows without a
successful serializer observation or a selected output premise. -/
theorem source (proof semantic y1 : Slice U8)
    (view : AspisR1SelectedWideViewV1.verifier.View)
    (call : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view)) :
    LPi_FieldValues.canonE (NBA_Carriers.back (AspisR1SelectedWideViewV1.preparedView view).inactive) ∧
    NBA_Installed.actual.sampling.toBytes (AspisR1SelectedWideViewV1.preparedView view).inactive =
      ok (AspisR1CurrentCaller.OriginalSerializerInstallation.expectedBytes
        (AspisR1SelectedWideViewV1.preparedView view).inactive) :=
  ⟨NBA_WideView.inactive proof semantic y1 view call,
    NCA_InactiveModel.source (AspisR1SelectedWideViewV1.preparedView view)⟩

#print axioms source
end AspisR1.NCA_InactiveDomain
