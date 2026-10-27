import RPv_FJk_ResidualWide
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PackedWide
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open FIz_ConcretePack (embed)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
attribute [local irreducible] R0P.poseidonScalarResidual
  R0P.poseidonLeadingPair R0P.poseidonInterpolatedFullPair R0P.poseidonInterpolatedInternalPair
/-- Complete evaluator value in Wide's literal packing basis. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hs : canonical s.local) (hb : Canon s.block)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    canonical out ∧ (fun g=>embed (decoded out g))=fun g=>R0P.pack4 ConcretePackBasis.basis
      (fun j=>R0P.poseidonScalarResidual
        (ValueFamilyFieldTransport.mapOpenings embed (FJh_Native07RawValue.openings o))
        (embed (decode s.block)) (fun i=>embed (decoded s.local i))
        (FJe_ExternalAdjoint.lane g j)) := by
  have v := FJk_Native07Value.value o s out hz ht hx hs hb run
  refine ⟨v.1,?_⟩
  funext g
  rw [v.2]
  rw [FJh_WidePack.value]
  apply congrArg (R0P.pack4 ConcretePackBasis.basis)
  funext j
  exact FJk_ResidualWide.scalar o s (FJe_ExternalAdjoint.lane g j)
#print axioms value
end AspisR1.FJk_PackedWide
end
