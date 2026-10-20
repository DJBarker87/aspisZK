import C2HostEmbedding
import AspisR1PublicPreparation.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.PreparedFromQmSourceBridge

abbrev PrepQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev PrepWide := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev HostQM := AspisC2HostEmbedding.field.QM31
abbrev HostWide := AspisC2HostEmbedding.field.wide_exact.WideExact

def prepToHostQM (q : PrepQM) : HostQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def hostToPrepWide (w : HostWide) : PrepWide :=
  ⟨⟨⟨w.c0.c0.a, w.c0.c0.b⟩, ⟨w.c0.c1.a, w.c0.c1.b⟩⟩,
    ⟨⟨w.c1.c0.a, w.c1.c0.b⟩, ⟨w.c1.c1.a, w.c1.c1.b⟩⟩⟩

def fromQmSource (q : PrepQM) : Result PrepWide := do
  let w ← AspisC2HostEmbedding.field.wide_exact.WideExact.from_qm31 (prepToHostQM q)
  ok (hostToPrepWide w)

def fromQmEmbedding (q : PrepQM) : PrepWide :=
  hostToPrepWide (AspisR1.C2HostEmbedding.embed (prepToHostQM q))

/-- Structural transport of the extracted current-core `WideExact::from_qm31`
body to the identically shaped Prepared field records.  Source pins for the
underlying function and canonicalizer are recorded separately in the packet. -/
theorem fromQmSource_success (q : PrepQM) :
    fromQmSource q = .ok (fromQmEmbedding q) := by
  unfold fromQmSource
  rw [AspisR1.C2HostEmbedding.embed_success]
  rfl

def withSourceFromQm (B : PreparedModel.Boundaries) : PreparedModel.Boundaries :=
  { B with fromQm := fromQmSource }

theorem withSourceFromQm_field (B : PreparedModel.Boundaries) :
    (withSourceFromQm B).fromQm = fromQmSource := rfl

theorem fromQmEmbedding_upper_zero (q : PrepQM) :
    (fromQmEmbedding q).c1 = AspisR1PublicPreparation.aspis_core.field.QM31.ZERO := by
  rfl

#print axioms fromQmSource_success
#print axioms withSourceFromQm_field
#print axioms fromQmEmbedding_upper_zero

end AspisR1PublicPreparation.PreparedFromQmSourceBridge
