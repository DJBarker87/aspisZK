import XRo_Join_Installed
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRq_FromQm

theorem canon (q : E.Q) : XRn_Join_FieldExternal.canon q =
 ok (eq (AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmEmbedding (cq q)).c0) := by
 unfold XRn_Join_FieldExternal.canon
 unfold AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmEmbedding
   AspisR1PublicPreparation.PreparedFromQmSourceBridge.hostToPrepWide
   AspisR1PublicPreparation.PreparedFromQmSourceBridge.prepToHostQM
   AspisR1.C2HostEmbedding.embed AspisR1.C2HostEmbedding.canonical
   AspisR1.C2HostEmbedding.reduce
 rfl

theorem source (q : E.Q) :
 aspis_core.field.wide_exact.WideExact.from_qm31 q =
 XRo_Join_Installed.actual.sampling.fromQm (cq q) := by
 change _ = AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmSource (cq q)
 rw [AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmSource_success]
 unfold aspis_core.field.wide_exact.WideExact.from_qm31
   aspis_core.field.wide_exact.WideExact.new
 rw [canon q,canon XRn_Join_FieldExternal.qzero]
 rfl
#print axioms canon
#print axioms source
end XRq_FromQm
