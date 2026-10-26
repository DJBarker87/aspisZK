import SAP_CanonicalCarrier
import F3M_SemanticSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_SampleCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem sample (block : Array U8 32#usize) (q : aspis_core.field.QM31)
    (success : sampler.qm31_sample block=ok q) : SAP_CanonicalCarrier.CanonK q := by
  obtain ⟨value,call,h,_⟩ := SamplerTransport.sample_total block
  have same : value=q := Result.ok.inj (call.symm.trans success)
  subst value
  exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩

theorem call {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) : SAP_CanonicalCarrier.CanonK c.q :=
  sample c.block c.q c.sample

theorem calls {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) :
    ∀ q ∈ cs.map SourceFull25.Call.q,SAP_CanonicalCarrier.CanonK q := by
  intro q h
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp h
  exact call c

#print axioms sample
#print axioms call
#print axioms calls
end AspisR1.SAP_SampleCanonical
end
