import NIT_RefInterpretation
import NIT_PairDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_NewPortInstantiation
open Aeneas Aeneas.Std Result NIT_Cuts NIT_RefInterpretation AspisR1Stage2

/-- On the actual returning NEW arm, its CLOSED output law supplies S2 and
constructor factor domains for exactly that child value. The native port cut
moves only its owner, and the same restricted input view reads its payload. -/
theorem returned (r : NP6_StdModel.Reservation) (proof : Slice U8) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (w : FIo_Install.W)
 (new : (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w))
 (alpha z owner : Nat) :
 ∃ before after : NewPort,
 cutNewPort p alpha z owner before after (.Ok ⟨owner,w⟩) ∧
 decode (⟨owner,w⟩ : Ref FIo_Install.W) owner=some w ∧
 NIT_PairDomain.Domain (FIo_Install.toWeights w) (NIT_PairDomain.alpha p)
  v.final_message (FIo_Install.toE p.kappa) := by
 have caller:=NIT_PairDomain.caller r proof v p a domain w new
 let before : NewPort:=⟨p.variant,alpha,z,some ⟨owner,w⟩,none,0⟩
 let after : NewPort:=⟨p.variant,alpha,z,none,none,1⟩
 refine ⟨before,after,?_,at_pointer _ _ rfl,caller⟩
 exact ⟨domain.s2,rfl,⟨⟨owner,w⟩,rfl,rfl,caller.s2⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms returned
end AspisR1.NIT_NewPortInstantiation
