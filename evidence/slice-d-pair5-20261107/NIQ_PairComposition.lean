import NIQ_AllocationError
import NIQ_FieldDomains
import NIG_PairCaller
import NIG_PairExport
set_option autoImplicit false
noncomputable section
namespace NIQ_PairComposition
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 LPi_FieldValues

/-- Discharge root-to-child domains from the SAME returned NEW owner and
primitive finish input. This is one returning cut, not pair success. -/
theorem caller_domains (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (w : FIo_Install.W)
 (new : (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z = ok (.Ok w)) :
 (FIo_Install.toWeights w).variant = FIo_Native.transport.Variant.S2 ∧
 NHI_TensorOuterStep.Factors (FIo_Install.toWeights w) ∧
 NHI_CellCanon.array (FIo_Install.toWeights w).extra ∧
 canonE (FIo_Install.toE p.kappa) ∧
 (∀ x ∈ (FIo_Install.toSlice p.alpha.to_slice).val, canonE x) ∧
 (∀ i, i < 64 → NIQ_FieldDomains.Domain v.final_message i) := by
 obtain ⟨s2,factors,extra⟩ := NIG_PairInputs.new_owner r proof v p a domain w new
 exact ⟨s2,factors,extra,NIG_FinishAlpha.canonical _ domain.kappa,
  NIG_PairInputs.alphas proof v p a domain,
  fun i hi => NIQ_FieldDomains.final proof v p a domain i hi⟩

/-- Complete allocator-error branch of the SAME pair packet. No allocation
availability or successful pair result is required. The native cut matching
this branch is NIQ allocation_error, not the timed-out NIG guard harness. -/
theorem allocation_packet (proof : Slice U8) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (w : FIo_Install.W)
 (e : NP6_StdModel.ReserveError) :
 NIG_PairExport.packet (.Err e) w p.alpha.to_slice v.final_message p.kappa =
 ok (.Err verifier.Error.Allocation) := by
 rw [←NIG_PairExport.source]
 unfold FIo_Install.pair
 rw [NIQ_AllocationError.source proof v p a domain (FIo_Install.toWeights w) e]
 rfl

-- The full native local-record interpretation is OPEN. No hypothesis equating
-- a chosen native output to packet is introduced here.
#print axioms caller_domains
#print axioms allocation_packet
end NIQ_PairComposition
