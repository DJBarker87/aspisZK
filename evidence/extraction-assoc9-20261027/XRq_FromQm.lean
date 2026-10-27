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
 have zero : XRn_Join_FieldExternal.canon XRn_Join_FieldExternal.qzero =
     ok XRn_Join_FieldExternal.qzero := by rfl
 rw [canon q,zero]
 simp only [bind_tc_ok]
 change ok (⟨cq (eq (AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmEmbedding (cq q)).c0),
   cq XRn_Join_FieldExternal.qzero⟩ : C.E) = _
 rw [cq_eq]
 have h := AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmEmbedding_upper_zero (cq q)
 unfold AspisR1PublicPreparation.aspis_core.field.QM31.ZERO at h
 change (AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmEmbedding (cq q)).c1 =
   cq XRn_Join_FieldExternal.qzero at h
 rw [←h]
#print axioms canon
#print axioms source
end XRq_FromQm
