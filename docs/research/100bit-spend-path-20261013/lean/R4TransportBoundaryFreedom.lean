import ExtractedPreparedModel

/-! The pinned Prepared adapter leaves the scalar output unconstrained.
This is an interface obstruction, not a Rust counterexample. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.R4TransportBoundaryFreedom
open Aeneas Aeneas.Std Result

def withGamma (B : PreparedModel.Boundaries) (out : aspis_core.field.WideExact) :
    PreparedModel.Boundaries := { B with gamma := fun _ => ok out }

/-- Even a successful actual block call and its exact returned state do not
constrain gamma at the free arithmetic boundary. -/
theorem arbitrary_gamma_success {Hash : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 Hash) (self after : transcript.Transcript Hash)
    (payload : Slice U8) (block : Array U8 32#usize)
    (hblock : transcript.Transcript.block D self 27#u8 payload = ok (block, after))
    (out : aspis_core.field.WideExact) :
    PreparedModel.scalar (withGamma B out) D self 27#u8 payload true = ok (out, after) := by
  simp only [PreparedModel.scalar, hblock, bind_tc_ok, Bool.true_eq, if_true,
    withGamma, lift, trace.value]
  rfl

/-- A universal output property at that interface is necessarily a property
of every machine value, rather than a fact about the nonzero sampler. -/
theorem universal_gamma_property {Hash : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 Hash) (self after : transcript.Transcript Hash)
    (payload : Slice U8) (block : Array U8 32#usize)
    (hblock : transcript.Transcript.block D self 27#u8 payload = ok (block, after))
    (property : aspis_core.field.WideExact → Prop)
    (h : ∀ (B' : PreparedModel.Boundaries) out,
      PreparedModel.scalar B' D self 27#u8 payload true = ok (out, after) → property out) :
    ∀ out, property out := by
  intro out
  exact h (withGamma B out) out (arbitrary_gamma_success B D self after payload block hblock out)

#print axioms arbitrary_gamma_success
#print axioms universal_gamma_property
end AspisR1PublicPreparation.R4TransportBoundaryFreedom
