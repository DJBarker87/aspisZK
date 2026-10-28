import R1Z.ProverRwRetryModel
import R1Z.ProverRwFullSampler

/-! Selected variant and sampler dictionary installation; actual rewritten
retrying_with is connected to the existing eight-attempt model. This does not
instantiate OS entropy, reservation IO, or the per-attempt model body. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwCallerBinding
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel ProverCommitSemanticTransport26
variable [ExternalTypes]

def variantEq : transport.Variant → transport.Variant → Result Bool
  | .S1,.S1 => ok true
  | .S2,.S2 => ok true
  | .D,.D => ok true
  | _,_ => ok false

theorem variant_exact (a b : transport.Variant) :
    variantEq a b = ok true ↔ a=b := by
  cases a <;> cases b <;> simp [variantEq]

@[reducible] def install (ops : ExternalFuns) : ExternalFuns :=
  { ProverRwFullSampler.install ops with op233 := variantEq }

section
variable (ops : ExternalFuns)

theorem admitted {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store : Store) (callback : C) :
    letI : ExternalFuns := install ops
    prover.prove_masked_retrying_with entropy pub compiled .S2 hash store callback =
      prover.retry_attempt entropy pub compiled .S2 hash store callback 0#usize := by
  letI : ExternalFuns := install ops
  simp only [prover.prove_masked_retrying_with,
    transport.Variant.Insts.CoreCmpPartialEqVariant,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,install,variantEq,bind_tc_ok,Bool.not_true,Bool.false_eq_true,if_false]
  rfl

theorem rejected_variant {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (notS2 : variant ≠ .S2)
    (hash : Hash) (store : Store) (callback : C) :
    letI : ExternalFuns := install ops
    prover.prove_masked_retrying_with entropy pub compiled variant hash store callback =
      ok (.Err verifier.Error.Semantic,store) := by
  letI : ExternalFuns := install ops
  cases variant <;> simp_all only [prover.prove_masked_retrying_with,
    transport.Variant.Insts.CoreCmpPartialEqVariant,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,install,variantEq,bind_tc_ok,Bool.not_false,if_true,ne_eq,not_true_eq_false] <;> rfl

theorem eight {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store : Store) (callback : C) :
    letI : ExternalFuns := install ops
    mapR sourceOutput (prover.prove_masked_retrying_with entropy pub compiled .S2 hash store callback) =
      mapR drop (ProverCommitRetry34.eight (attempt entropy pub compiled .S2 hash) (callback,store)) := by
  letI : ExternalFuns := install ops
  rw [admitted ops]
  exact retry entropy pub compiled .S2 hash store callback 0#usize 8 (by rfl)

#print axioms admitted
#print axioms rejected_variant
#print axioms eight
end
#print axioms variant_exact
end R1Z.ProverRwCallerBinding
