import PV_B3P_ByteTotal226V3
import PV_B3P_EncodeSuccess226V3
import PV_B3P_ZeroSource226V3
import PV_B3P_Install226V3
namespace PV_B3P_Nonvacuity226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ZeroSource226V3
set_option autoImplicit false
noncomputable section

theorem canonical (b : Bool) : PV_B3P_ByteTotal226V3.Canonical (owned b) := by
  constructor
  · exact canonical_digest
  · exact canonical_digest
  · change (0#u32) < 2147483647#u32; decide
  · exact canonical_digest
  · exact canonical_digest
  · change (0#u32) < 2147483647#u32; decide
  · exact canonical_frontier
  · exact canonical_digest
  · exact canonical_frontier

theorem reference_success (b : Bool) :
    ∃ out, reference226.public_bytes (source b) = .ok (.Ok out) := by
  obtain ⟨out,hout⟩ := PV_B3P_EncodeSuccess226V3.success (owned b)
    (fun i => PV_B3P_ByteTotal226V3.success (owned b) i (canonical b))
  refine ⟨out,?_⟩
  unfold reference226.public_bytes
  rw [projection]
  exact hout

theorem installed_success (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_B3P_Install226V3.Types base)) (b : Bool) :
    ∃ p out, @ProverRwFull.ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out) := by
  obtain ⟨⟨chunks,n⟩,hh⟩ := reference_success b
  refine ⟨PV_B3P_PublicCarrier226V3.fromSource base (source b),
    PV_B3P_ByteOutput226.bytes chunks n,?_⟩
  rw [PV_B3P_Install226V3.source,PV_B3P_PublicCarrier226V3.reverse_roundtrip,hh]
  rfl

#print axioms canonical
#print axioms reference_success
#print axioms installed_success
end
end PV_B3P_Nonvacuity226V3
