import R1Z.PV_RE_ShapePoison
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ShapeRejection
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_ShapePoison
variable [ExternalTypes]
/-- The explicit equality-rejection branch preserves the store and returns a
native Err inside outer ok. No later whole run is normalized. -/
theorem equality_rejected {C : Type} (D : ExternalFuns)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C)
    (h : D.op233 .S2 .S2 = .ok false) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      .ok (.Err .Semantic, store) := by
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
    core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
    transport.Variant.Insts.CoreCmpPartialEqVariant
  simp only [PV_RE_ShapePoison.bind_assoc, h]
  rfl

/-- A divergent first callback also propagates through the actual caller. -/
theorem entry_diverges {C : Type} (D : ExternalFuns)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C)
    (h : D.op233 .S2 .S2 = .div) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state = .div := by
  obtain ⟨next, hn⟩ := PV_RE_ShapePoison.entry D entropy pub compiled hash store state
  rw [hn, h]
  rfl

#print axioms equality_rejected
#print axioms entry_diverges
end R1Z.PV_RE_ShapeRejection
