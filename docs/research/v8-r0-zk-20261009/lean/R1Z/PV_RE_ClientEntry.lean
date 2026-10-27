import R1Z.PV_RE_AttemptEntry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientEntry
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_AttemptEntry
variable [ExternalTypes]
abbrev ClientReply := Result ((core.result.Result prover.RetriedProof verifier.Error) × Store)

theorem bind_assoc {A B C : Type} (x : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  cases x <;> rfl

/-- Before entropy admission and before op226, the extracted proof-account
caller calls the variant equality callback. The suffix is kept symbolic. -/
theorem first {S : Type} (ops : ExternalFuns)
    (entropy : core.ops.function.FnMut S Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : S) :
    ∃ next : Bool → ClientReply,
      @RealR1_client.prove_for_proof_accounts _ ops S entropy pub compiled hash store state =
        (ops.op233 .S2 .S2 >>= next) := by
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
    core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default transport.Variant.Insts.CoreCmpPartialEqVariant
  simp only [bind_assoc]
  exact ⟨_,rfl⟩

#print axioms bind_assoc
#print axioms first
end R1Z.PV_RE_ClientEntry
