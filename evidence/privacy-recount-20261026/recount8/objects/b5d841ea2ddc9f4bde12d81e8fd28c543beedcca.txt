import R1Z.ProverCommitReservationMemo37
import R1Z.ProverCommitEntropy18

/-! Conditioning away zero nonces and following the actual rejection owner
cannot turn a reservation-input query into a simulator seed-domain query. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationNonzero37
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitReservationRom37 ProverCommitEntropy18 GamesR1PBin
local instance (priority := 10000) allDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
local instance (priority := 10000) allDecEq (U : Type) : DecidableEq U := Classical.decEq U

def mixedHit {A U : Type} (known : A) (entry : U)
    (r : A × ({j : A // j ≠ known} → U)) : Prop :=
  (LazyTable.splitAt known).symm (entry,r.2) r.1 = entry

theorem mixed_memo_mass {A U : Type} [Fintype A] [Nonempty A]
    [Fintype U] [Nonempty U] (known : A) (entry : U) :
    eventMass (mixedHit known entry) =
      1 / (Fintype.card U : ℚ) +
        (1 / (Fintype.card A : ℚ)) * (1 - 1 / (Fintype.card U : ℚ)) := by
  unfold eventMass mixedHit
  rw [R0Z.LawTransport.mean_product]
  have inner (nonce : A) :
      mean (fun rest : {j : A // j ≠ known} → U =>
        if (LazyTable.splitAt known).symm (entry,rest) nonce = entry then (1 : ℚ) else 0) =
      if nonce = known then 1 else 1 / (Fintype.card U : ℚ) := by
    by_cases hn : nonce = known
    · subst nonce
      simp [LazyTable.splitAt,mean_const]
    · have uniform := QueryScanSharedHistoryMass.eval_point_mass
        (U := U) (⟨nonce,hn⟩ : {j : A // j ≠ known}) entry
      simpa [eventMass,LazyTable.splitAt,hn] using uniform
  simp only [inner]
  have shape (nonce : A) :
      (if nonce = known then (1 : ℚ) else 1 / (Fintype.card U : ℚ)) =
      (if nonce = known then (1 : ℚ) else 0) * (1 - 1 / (Fintype.card U : ℚ)) +
        1 / (Fintype.card U : ℚ) := by
    have algebra (p : ℚ) (h : Prop) [Decidable h] :
        (if h then 1 else p) = (if h then 1 else 0) * (1-p) + p := by
      split_ifs <;> ring
    exact algebra _ _
  simp_rw [shape]
  rw [R0Z.FsAbortBounds.mean_add'',R0Z.FsAbortBounds.mean_mul_const,mean_const]
  have pointmean : mean (fun nonce : A => if nonce = known then (1 : ℚ) else 0) =
      1 / (Fintype.card A : ℚ) := QueryScanSharedHistoryMass.point_mass known
  rw [pointmean]
  ring

/-- This counterexample survives even an ideal exact-uniform nonzero nonce.
No conditioning loss or exhausted draw is asserted to have disappeared. -/
theorem nonzero_memo_exceeds (known : NZ) (entry : OracleAnswer) :
    1 / (2 : ℚ)^256 < eventMass (mixedHit known entry) := by
  have h := mixed_memo_mass known entry
  have card : Fintype.card OracleAnswer = 2^256 := by
    have all : ∀ j : Fintype OracleAnswer, @Fintype.card OracleAnswer j = 2^256 := fun j =>
      (congrArg (@Fintype.card OracleAnswer) (Subsingleton.elim j _)).trans
        QueryScanSharedHistoryMass.answer_cardinality
    exact all _
  rw [card,Nat.cast_pow,Nat.cast_ofNat] at h
  rw [h]
  have hp : 0 < 1 / (Fintype.card NZ : ℚ) := by
    apply one_div_pos.mpr
    exact_mod_cast Fintype.card_pos
  have hd : 0 < 1 - 1 / (2 : ℚ)^256 := by norm_num
  exact lt_add_of_pos_right _ (mul_pos hp hd)

attribute [-instance] allDecidable allDecEq
attribute [local instance] Classical.propDecidable

def countdownNext (secret : SecP) (remaining : Nat) : Except Unit Candidate × Nat :=
  if remaining = 0 then (.ok (fun i => (secret i).val),0)
  else (.ok (fun _ => 0),remaining-1)

/-- Exactly `rejects` all-zero candidates followed by a successful nonzero
96-byte candidate; arbitrary remaining fuel is retained. -/
theorem rejected_prefix_success (secret : SecP) (rejects fuel : Nat) :
    run (countdownNext secret) (rejects+fuel+1) rejects = (.ok secret,0) := by
  induction rejects with
  | zero =>
    simpa only [Nat.zero_add] using
      success (countdownNext secret) 0 0 secret fuel (by simp [countdownNext])
  | succ rejects ih =>
    have step : countdownNext secret (rejects+1) = (.ok (fun _ => 0),rejects) := by
      simp [countdownNext]
    simp only [run,step,decode_zero]
    rw [show rejects+1+fuel = rejects+fuel+1 by omega]
    exact ih

/-- All legal rejected-prefix lengths 0..15 still exhibit the exact missing
query-event containment at the native generator's successful return. -/
theorem retry_query_not_covered (secret : SecP) (seed : OracleAnswer)
    (rejects : Nat) (bound : rejects < 16) :
    generate (countdownNext secret) rejects = (.ok secret,0) ∧
      (secret 0).val ≠ 0 ∧
      reservationQueried [(reservationInput (secret 0).val,0)] (secret 0).val ∧
      ¬ ProverCommitSeedEvent19.seedGuess [(reservationInput (secret 0).val,0)] seed := by
  refine ⟨?_,(secret 0).property,queried_not_seedGuess (secret 0).val seed⟩
  unfold generate
  have fuel : 16 = rejects+(15-rejects)+1 := by omega
  rw [fuel]
  exact rejected_prefix_success secret rejects (15-rejects)

#print axioms mixed_memo_mass
#print axioms nonzero_memo_exceeds
#print axioms rejected_prefix_success
#print axioms retry_query_not_covered
end R1Z.ProverCommitReservationNonzero37
