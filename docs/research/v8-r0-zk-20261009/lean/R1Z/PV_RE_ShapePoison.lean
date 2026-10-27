import R1Z.ProverRwFullFuns
import R1Z.PV_RE_NoCatchCore
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ShapePoison
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Reply := Result ((core.result.Result prover.RetriedProof verifier.Error) × Store)

def poison233 (D : ExternalFuns) (e : Error) : ExternalFuns :=
  { D with op233 := fun _ _ => .fail e }

theorem bind_assoc {A B C : Type} (x : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  cases x <;> rfl

/-- Directly expose only the extracted caller's first bind. -/
theorem entry {C : Type} (D : ExternalFuns)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    ∃ next : Bool → Reply,
      @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
        (D.op233 .S2 .S2 >>= next) := by
  unfold RealR1_client.prove_for_proof_accounts prover.prove_masked_retrying_with
    core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
    transport.Variant.Insts.CoreCmpPartialEqVariant
  simp only [bind_assoc]
  exact ⟨_,rfl⟩

/-- Every shape and input fails at entry under op233 poisoning. -/
theorem poisoned_entry {C : Type} (D : ExternalFuns) (e : Error)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    @RealR1_client.prove_for_proof_accounts _ (poison233 D e) C entropy pub compiled hash store state =
      .fail e := by
  obtain ⟨next, h⟩ := entry (poison233 D e) entropy pub compiled hash store state
  rw [h]
  rfl

/-- Any admitted successful input, once supplied, witnesses op233 necessity.
This is conditional and does not assert fixture success/non-vacuity. -/
theorem success_distinguishes {C : Type} (D : ExternalFuns) (e : Error)
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (pub : Public) (compiled : Compiled) (hash : Hash) (store : Store) (state : C)
    (v : (core.result.Result prover.RetriedProof verifier.Error) × Store)
    (h : @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state = .ok v) :
    @RealR1_client.prove_for_proof_accounts _ (poison233 D e) C entropy pub compiled hash store state ≠
      @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state := by
  rw [poisoned_entry, h]
  intro impossible
  cases impossible

#print axioms poison233
#print axioms bind_assoc
#print axioms entry
#print axioms poisoned_entry
#print axioms success_distinguishes
end R1Z.PV_RE_ShapePoison
