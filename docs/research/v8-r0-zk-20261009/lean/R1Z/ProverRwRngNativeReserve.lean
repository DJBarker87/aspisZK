import R1Z.ProverRwRngNativeBodyEmission
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngNativeReserve
open Aeneas Aeneas.Std Result ProverRwRngNativeBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding
variable [TypeLeaves] [LocalLeaves]
abbrev Secrets := StateOnlyAttemptSecrets
abbrev Context := StateOnlyHidingContext
abbrev BuildError := StateOnlyMaskBuildError
abbrev Store (S : Type) := StateOnlyMaskNonceStore S
abbrev reserveBuild {S : Type} := @StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1 _ _ S
abbrev acknowledge := PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)

omit [TypeLeaves] [LocalLeaves] in
theorem mask_error_exact (e : BuildError) :
    prover.mask_error e = .ok (match e with
      | .MaskSampleExhausted => verifier.Error.Rejected
      | _ => verifier.Error.Semantic) := by
  cases e <;> simp [prover.mask_error,
    StateOnlyMaskBuildError.Insts.CoreCmpPartialEqStateOnlyMaskBuildError.eq, StateOnlyMaskBuildError.read_discriminant]

omit [TypeLeaves] [LocalLeaves] in
theorem acknowledgment_single_use (p : PreReservedNonce)
    (statement nonce : Array U8 32#usize) (used : p.consumed = true) :
    acknowledge p statement nonce = .ok (false,p) := by
  simp only [acknowledge,PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve,
    used,if_true]

omit [TypeLeaves] [LocalLeaves] in
theorem byte_ne_self (x : U8) : core.cmp.PartialEqU8.ne x x = .ok false := by
  simp [core.cmp.PartialEqU8]

omit [TypeLeaves] [LocalLeaves] in
theorem list_compare_self (xs : List U8) :
    List.allM (fun xy : U8 × U8 =>
      Result.ok (decide (¬ core.cmp.impls.PartialEqU8.ne xy.1 xy.2)))
      (xs.zip xs) = Result.ok true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa [List.zip_cons_cons,List.allM] using ih

omit [TypeLeaves] [LocalLeaves] in
theorem array_ne_self {N : Usize} (a : Array U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a = .ok false := by
  unfold core.array.equality.PartialEqArray.ne core.array.equality.PartialEqArray.eq
  simp only [ite_true, list_compare_self, bind_tc_ok]
  rfl

#print axioms list_compare_self
#print axioms array_ne_self
#print axioms mask_error_exact
#print axioms acknowledgment_single_use
#print axioms byte_ne_self
end R1Z.ProverRwRngNativeReserve
