import R1Z.ProverCommitReservationRom37

/-! Exact conditional ROM counterexample to charging reservation memo hits
only to the existing simulator-domain seed event. One prior query, one
entry chosen as its answer; the nonce is still independent uniform. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationMemo37
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitReservationRom37
local instance (priority := 10000) allDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
local instance (priority := 10000) allDecEq (U : Type) : DecidableEq U := Classical.decEq U

/-- After a prior query at `known` has answer `entry`, the other coordinates
remain uniform. This is a conditional ROM slice, not a constant hash model.
The adversary inserts exactly the learned answer in its initial ledger. -/
def memoHit {U : Type} (known entry : U)
    (r : U × ({j : U // j ≠ known} → U)) : Prop :=
  (LazyTable.splitAt known).symm (entry,r.2) r.1 = entry

theorem generic_memo_mass {U : Type} [Fintype U] [Nonempty U]
    (known entry : U) :
    eventMass (memoHit known entry) =
      2 * (1 / (Fintype.card U : ℚ)) - (1 / (Fintype.card U : ℚ))^2 := by
  classical
  unfold eventMass memoHit
  rw [R0Z.LawTransport.mean_product]
  have inner (nonce : U) :
      mean (fun rest : {j : U // j ≠ known} → U =>
        if (LazyTable.splitAt known).symm (entry,rest) nonce = entry then (1 : ℚ) else 0) =
      if nonce = known then 1 else 1 / (Fintype.card U : ℚ) := by
    by_cases hn : nonce = known
    · subst nonce
      simp [LazyTable.splitAt,mean_const]
    · have uniform := QueryScanSharedHistoryMass.eval_point_mass
        (U := U) (⟨nonce,hn⟩ : {j : U // j ≠ known}) entry
      simpa [eventMass,LazyTable.splitAt,hn] using uniform
  simp only [inner]
  have shape (nonce : U) :
      (if nonce = known then (1 : ℚ) else 1 / (Fintype.card U : ℚ)) =
      (if nonce = known then (1 : ℚ) else 0) * (1 - 1 / (Fintype.card U : ℚ)) +
        1 / (Fintype.card U : ℚ) := by
    have algebra (p : ℚ) (h : Prop) [Decidable h] :
        (if h then 1 else p) = (if h then 1 else 0) * (1-p) + p := by
      split_ifs <;> ring
    exact algebra _ _
  simp_rw [shape]
  rw [R0Z.FsAbortBounds.mean_add'',R0Z.FsAbortBounds.mean_mul_const,mean_const]
  have pointmean : mean (fun nonce : U => if nonce = known then (1 : ℚ) else 0) =
      1 / (Fintype.card U : ℚ) := QueryScanSharedHistoryMass.point_mass known
  rw [pointmean]
  ring

theorem conditional_memo_mass (known entry : OracleAnswer) :
    eventMass (memoHit known entry) =
      2 / (2 : ℚ)^256 - (1 / (2 : ℚ)^256)^2 := by
  have h := generic_memo_mass known entry
  have card : Fintype.card OracleAnswer = 2^256 := by
    have all : ∀ j : Fintype OracleAnswer, @Fintype.card OracleAnswer j = 2^256 := fun j =>
      (congrArg (@Fintype.card OracleAnswer) (Subsingleton.elim j _)).trans
        QueryScanSharedHistoryMass.answer_cardinality
    exact all _
  rw [card,Nat.cast_pow,Nat.cast_ofNat] at h
  rw [mul_one_div] at h
  exact h

/-- The single-entry 2^-256 bound fails when the memo-hit event is omitted.
The failure occurs before any rejection conditioning. -/
theorem memo_exceeds_fresh_bound (known entry : OracleAnswer) :
    1 / (2 : ℚ)^256 < eventMass (memoHit known entry) := by
  rw [conditional_memo_mass]
  have hp : 0 < 1 / (2 : ℚ)^256 := by positivity
  have hlt : 1 / (2 : ℚ)^256 < 1 := by norm_num
  rw [show 2 / (2 : ℚ)^256 = 2 * (1 / (2 : ℚ)^256) from (mul_one_div _ _).symm]
  generalize (1 / (2 : ℚ)^256) = p at *
  nlinarith

/-- The exact prior-query list in this ROM slice never triggers the old
simulator event, for any independent simulator seed. Nonzero filtering of
the nonce does not change this pointwise event disjointness. -/
theorem old_event_absent (known entry seed : OracleAnswer) :
    ¬ ProverCommitSeedEvent19.seedGuess [(reservationInput known,entry)] seed := by
  rintro ⟨q,member,point⟩
  have eq : q = (reservationInput known,entry) := by simpa using member
  subst q
  exact not_simulator_seedPoint known seed point

#print axioms generic_memo_mass
#print axioms conditional_memo_mass
#print axioms memo_exceeds_fresh_bound
#print axioms old_event_absent
end R1Z.ProverCommitReservationMemo37
