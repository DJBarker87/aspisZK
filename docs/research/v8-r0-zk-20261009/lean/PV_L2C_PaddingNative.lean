import PV_L2C_QFold
set_option autoImplicit false
namespace PV_L2C_PaddingNative
open PV_L2C_NativeQ PV_L2C_QFold
open PV_L2C_PaddingProducer

def without {n : Nat} (d : Fin n) (table : Fin n → Q) : Fin n → Q :=
  fun i => if i=d then zero else table i

def excluded {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q) : Q :=
  tableSum (inactiveTable active (without d table))

def rebalance {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q) : Fin n → Q :=
  fun i => if i=d then subQ zero (excluded active d table) else table i

def sample {n : Nat} (active : Fin n → Bool) (d : Fin n) (random : Fin n → Q) : Fin n → Q :=
  fun i => if active i || decide (i=d) then zero else random i

theorem without_canonical {n : Nat} (d : Fin n) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) : ∀ i, Canonical (without d table i) := by
  intro i
  by_cases hi : i=d <;> simp [without,hi,zero_canonical,hc i]
#print axioms without_canonical

theorem excluded_canonical {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) : Canonical (excluded active d table) :=
  tableSum_canonical _ (inactive_canonical active _ (without_canonical d table hc))
#print axioms excluded_canonical

theorem rebalance_canonical {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) : ∀ i, Canonical (rebalance active d table i) := by
  intro i
  by_cases hi : i=d
  · simp only [rebalance,hi,if_pos]
    exact sub_canonical _ _ zero_canonical (excluded_canonical active d table hc)
  · simpa [rebalance,hi] using hc i
#print axioms rebalance_canonical

theorem excluded_decode {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) :
    decodeQ (excluded active d table)=excludedSum active d (fun i => decodeQ (table i)) := by
  rw [excluded,inactive_decode active _ (without_canonical d table hc)]
  unfold inactiveSum excludedSum
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hid : i=d <;> cases ha : active i <;> simp [without,hid,ha,zero_decode]
#print axioms excluded_decode

theorem rebalance_decode {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) (i : Fin n) :
    decodeQ (rebalance active d table i)=balanced active d (fun i => decodeQ (table i)) i := by
  by_cases hi : i=d
  · simp only [rebalance,hi,if_pos,balanced]
    rw [sub_decode _ _ zero_canonical (excluded_canonical active d table hc),
      zero_decode,zero_sub,excluded_decode active d table hc]
  · simp [rebalance,balanced,hi]
#print axioms rebalance_decode

/-- Actual four-limb inactive sum is raw zero after the negative-sum store,
for arbitrary canonical prior values and arbitrary public inactive geometry. -/
theorem raw_sum_zero {n : Nat} (active : Fin n → Bool) (d : Fin n) (table : Fin n → Q)
    (hc : ∀ i, Canonical (table i)) (hd : active d=false) :
    tableSum (inactiveTable active (rebalance active d table))=zero := by
  have hcan := rebalance_canonical active d table hc
  apply decode_injective _ _ (tableSum_canonical _ (inactive_canonical active _ hcan)) zero_canonical
  rw [inactive_decode active _ hcan,zero_decode]
  have he : (fun i => decodeQ (rebalance active d table i))=
      balanced active d (fun i => decodeQ (table i)) := by
    funext i
    exact rebalance_decode active d table hc i
  rw [he]
  exact balanced_sum active d _ hd
#print axioms raw_sum_zero

theorem sample_canonical {n : Nat} (active : Fin n → Bool) (d : Fin n) (random : Fin n → Q)
    (hc : ∀ i, Canonical (random i)) : ∀ i, Canonical (sample active d random i) := by
  intro i
  unfold sample
  split <;> simp_all [zero_canonical]
#print axioms sample_canonical

theorem active_zero {n : Nat} (active : Fin n → Bool) (d : Fin n) (random : Fin n → Q)
    (hd : active d=false) (i : Fin n) (hi : active i=true) :
    rebalance active d (sample active d random) i=zero := by
  have hid : i≠d := by intro h; subst i; rw [hd] at hi; contradiction
  simp [rebalance,sample,hid,hi]
#print axioms active_zero

/-- N2's two native rejection predicates, with no zero-sum hypothesis. -/
theorem guard_outcomes {n : Nat} (active : Fin n → Bool) (d : Fin n) (random : Fin n → Q)
    (hc : ∀ i, Canonical (random i)) (hd : active d=false) :
    (∀ i, active i && decide (rebalance active d (sample active d random) i≠zero)=false) ∧
    decide (tableSum (inactiveTable active (rebalance active d (sample active d random)))≠zero)=false := by
  constructor
  · intro i
    cases hi : active i with
    | false => simp [hi]
    | true => rw [active_zero active d random hd i hi]; simp
  · rw [raw_sum_zero active d _ (sample_canonical active d random hc) hd]
    rfl
#print axioms guard_outcomes
end PV_L2C_PaddingNative
