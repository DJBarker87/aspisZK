import R1Z.SimCostRelativeObstruction

/-! A fixed-statement callback boundary. This strengthens the earlier varying-
statement obstruction in a different quantifier order: the statement is fixed,
but no one numerical byte-emission tariff covers all permitted callbacks.
It does not rule out a bound for one specified callback and fixed statement. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostCallbacks6
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.RefPayload R1Z.Batched
  R1Z.SimCostWriter R1Z.SimCostRelativeObstruction
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis

/-- A concrete callback family; each member has constant output length. -/
def bytes (m : Nat) : Statement K Nat → Challenges K → List UInt8 :=
  fun _ _ => List.replicate m 0

theorem metadata_output_cost (m : Nat) (x : Statement K Nat) (ch : Challenges K) :
    (emit (ZkStatement.metadata (bytes m) x ch).publicOutputs).2 = m := by
  rw [emit_cost]
  exact List.length_replicate

theorem view_output_cost (m : Nat) (π : Fin 1024 ≃ Fin 1024)
    (x : Statement K Nat) (ch : Challenges K) (t : Tape K F) :
    (emit ((simE (Bat := R1Bat) π B (bytes m) x ch t).1.publicOutputs)).2 = m := by
  rw [emit_cost]
  exact List.length_replicate

/-- Keep public input, field, basis, challenges and tape fixed. Only the
permitted callback varies. This is a byte-emission lower bound, not a lower
bound on a lazy pair or on the unconstrained Writer.Stage data structure. -/
theorem no_uniform_callback_tariff (π : Fin 1024 ≃ Fin 1024)
    (x : Statement K Nat) (ch : Challenges K) (t : Tape K F) (C : Nat) :
    ∃ outputs : Statement K Nat → Challenges K → List UInt8,
      C < (emit ((simE (Bat := R1Bat) π B outputs x ch t).1.publicOutputs)).2 := by
  refine ⟨bytes (C+1), ?_⟩
  rw [view_output_cost]
  exact Nat.lt_succ_self C

/-- Even with the statement fixed, the complete desired polynomial's value at
any supplied relative adversary-input size can be exceeded by a callback. -/
theorem no_uniform_callback_relative_bound (π : Fin 1024 ≃ Fin 1024)
    (x : Statement K Nat) (ch : Challenges K) (t : Tape K F) (n c k d : Nat) :
    ∃ outputs : Statement K Nat → Challenges K → List UInt8,
      c * (n+k)^d <
        (emit ((simE (Bat := R1Bat) π B outputs x ch t).1.publicOutputs)).2 :=
  no_uniform_callback_tariff π x ch t (c*(n+k)^d)

#print axioms metadata_output_cost
#print axioms view_output_cost
#print axioms no_uniform_callback_tariff
#print axioms no_uniform_callback_relative_bound
end R1Z.SimCostCallbacks6
